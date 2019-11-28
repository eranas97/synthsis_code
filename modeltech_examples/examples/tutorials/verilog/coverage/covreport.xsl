<xsl:stylesheet version="1.0" xmlns:xsl="http://www.w3.org/1999/XSL/Transform">
<xsl:output method="text" encoding="UTF-8"/>

<xsl:template match="/">
  <xsl:apply-templates/>
</xsl:template>

<xsl:template match="report">
  <xsl:if test="@summary">
  Summary Mode: 
  </xsl:if>
  <xsl:if test="@zeros">
  Mode to display objects having zero counts:
  </xsl:if>
  <xsl:if test="@lines">
  Mode to display individual lines:
  </xsl:if>
  <xsl:if test="@sourcePath">
  Report only on file: <xsl:value-of select="@sourcePath"/>
  </xsl:if>
  <xsl:if test="@instancePath">
  Report only on instance: <xsl:value-of select="@instancePath"/>
  </xsl:if>
  <xsl:if test="@all">
  Display all toggle signals:
  </xsl:if>
  <xsl:if test="@totals">
  Display only totals:
  </xsl:if>
  <xsl:if test="@byInstance">
  Report by Instance:
  </xsl:if>
  <xsl:apply-templates/>
</xsl:template>

<xsl:template match="toggleSummary">
  Summary of signals toggled:
    Total Signals: <xsl:value-of select="@total"/>
    Num Toggled  : <xsl:value-of select="@toggled"/>
    Percent      : <xsl:value-of select="@percent"/>
</xsl:template>

<xsl:template match="tog">
  Signal : <xsl:value-of select="@name"/>
    To Zero: <xsl:value-of select="@c0"/>
    To One : <xsl:value-of select="@c1"/>
</xsl:template>

<xsl:template match="toge">
  Signal : <xsl:value-of select="@name"/>
    One To Zero: <xsl:value-of select="@c1H_0L"/>
    Zero To One: <xsl:value-of select="@c0L_1H"/>
    Zero To Unk: <xsl:value-of select="@c0L_XZ"/>
    Unk To Zero: <xsl:value-of select="@cXZ_0L"/>
    One To Unk : <xsl:value-of select="@c1H_XZ"/>
    Unk To One : <xsl:value-of select="@cXZ_1H"/>
</xsl:template>

<xsl:template match="summaryByFile">
  Summary of coverage by File:
    Number of Files: <xsl:value-of select="@files"/>
  <xsl:apply-templates/>
</xsl:template>

<xsl:template match="summaryByInstance">
  Summary of coverage by Instance:
    Number of Instances: <xsl:value-of select="@instances"/>
  <xsl:apply-templates/>
</xsl:template>

<xsl:template match="statements">
  Statements:
    Active : <xsl:value-of select="@active"/>
    Hits   : <xsl:value-of select="@hits"/>
    Percent: <xsl:value-of select="@percent"/>
</xsl:template>

<xsl:template match="branches">
  Branches:
    Active : <xsl:value-of select="@active"/>
    Hits   : <xsl:value-of select="@hits"/>
    Percent: <xsl:value-of select="@percent"/>
</xsl:template>

<xsl:template match="conditions">
  Conditions:
    Active : <xsl:value-of select="@active"/>
    Hits   : <xsl:value-of select="@hits"/>
    Percent: <xsl:value-of select="@percent"/>
</xsl:template>

<xsl:template match="expressions">
  Expressions:
    Active : <xsl:value-of select="@active"/>
    Hits   : <xsl:value-of select="@hits"/>
    Percent: <xsl:value-of select="@percent"/>
</xsl:template>

<xsl:template match="fileData">
  Coverage by File:
    File path: <xsl:value-of select="@path"/>
  <xsl:apply-templates/>
</xsl:template>

<xsl:template match="instanceData">
  Coverage by Instance:
    Instance path: <xsl:value-of select="@path"/>
    Design unit: <xsl:value-of select="@du"/>
  <xsl:apply-templates/>
</xsl:template>

<xsl:template match="file">
  Data for file: <xsl:value-of select="@path"/>
  <xsl:apply-templates/>
</xsl:template>

<xsl:template match="stmt">
  Statement: <xsl:if test="@fn">
    File number: <xsl:value-of select="@fn"/></xsl:if>
    Line number: <xsl:value-of select="@ln"/>
    Stmt number: <xsl:value-of select="@st"/>
    Hit count  : <xsl:value-of select="@hits"/>
</xsl:template>

<xsl:template match="if">
  Branch coverage for IF statement:
    Active branches: <xsl:value-of select="@active"/>
    Branches hit   : <xsl:value-of select="@hits"/>
    Percent for IF : <xsl:value-of select="@percent"/>
  <xsl:apply-templates/>
</xsl:template>

<xsl:template match="ielem">
  IF statement element: <xsl:if test="@fn">
    File number: <xsl:value-of select="@fn"/></xsl:if>
    Line number: <xsl:value-of select="@ln"/>
    Stmt number: <xsl:value-of select="@st"/>
    True hits  : <xsl:value-of select="@true"/>
    False hits : <xsl:value-of select="@false"/>
</xsl:template>

<xsl:template match="case">
  Branch coverage for CASE statement:
    Active branches : <xsl:value-of select="@active"/>
    Branches hit    : <xsl:value-of select="@hits"/>
    Percent for CASE: <xsl:value-of select="@percent"/>
  <xsl:apply-templates/>
</xsl:template>

<xsl:template match="celem">
  CASE statement element: <xsl:if test="@fn">
    File number: <xsl:value-of select="@fn"/></xsl:if>
    Line number: <xsl:value-of select="@ln"/>
    Stmt number: <xsl:value-of select="@st"/>
    Num hits   : <xsl:value-of select="@hits"/>
</xsl:template>

<xsl:template match="condition">
  Condition: <xsl:if test="@fn">
    File number: <xsl:value-of select="@fn"/></xsl:if>
    Line number: <xsl:value-of select="@ln"/>
    Stmt number: <xsl:value-of select="@st"/>
    Num terms  : <xsl:value-of select="@active"/>
    Terms hit  : <xsl:value-of select="@hits"/>
    Percent    : <xsl:value-of select="@percent"/>
</xsl:template>

<xsl:template match="expression">
  Expression: <xsl:if test="@fn">
    File number: <xsl:value-of select="@fn"/></xsl:if>
    Line number: <xsl:value-of select="@ln"/>
    Stmt number: <xsl:value-of select="@st"/>
    Num terms  : <xsl:value-of select="@active"/>
    Terms hit  : <xsl:value-of select="@hits"/>
    Percent    : <xsl:value-of select="@percent"/>
</xsl:template>

<xsl:template match="table">
  Truth Table:
    Number of rows: <xsl:value-of select="@rows"/>
    Number of cols: <xsl:value-of select="@cols"/>
    Unknown cases : <xsl:value-of select="@unknown"/>
  <xsl:apply-templates/>
</xsl:template>

<xsl:template match="col">
  col: <xsl:value-of select="@i"/> label: <xsl:value-of select="@label"/>
</xsl:template>

<xsl:template match="row">
  row: <xsl:value-of select="@i"/> hits: <xsl:value-of select="@hits"/> body: <xsl:value-of select="@body"/>
</xsl:template>

<xsl:template match="sourceTable">
  Table of Source Files for Design Unit: Number of files: <xsl:value-of select="@files"/>
  <xsl:apply-templates/>
</xsl:template>

<xsl:template match="fileMap">
  File mapping: File number <xsl:value-of select="@fn"/> Path: <xsl:value-of select="@path"/>
</xsl:template>

</xsl:stylesheet>

