module SPLTheory where


data Model = Basic |                -- vra
             Composite Model Model  -- vra

data Property = SomeValue;

data Option;

type Conf = Option -> Bool

type  AnalyzeModelCompositeShell = Property -> Property -> Property

analyzeModelCompositeShell :: AnalyzeModelCompositeShell 
analyzeModelCompositeShell _ _ = SomeValue

data VarModel = ModelBase Model | 
                ModelChoice Option VarModel VarModel |
                ModelComposite   VarModel  VarModel


data VarProperty = PropertyBase Property | 
                   PropertyChoice Option VarProperty VarProperty | 
                   PropertyComposite AnalyzeModelCompositeShell VarProperty  VarProperty ;  --vra


varJoinProperty :: Option -> VarProperty -> VarProperty -> VarProperty
varJoinProperty o vp1 vp2 = PropertyChoice o vp1 vp2

varCompositeProperty ::  VarProperty -> VarProperty -> VarProperty
varCompositeProperty vp1 vp2 = PropertyComposite analyzeModelCompositeShell vp1 vp2

projectProperty :: VarProperty -> Conf -> Property
projectProperty (PropertyChoice o vp1 vp2) c = if c o then projectProperty vp1 c else projectProperty vp2 c
projectProperty (PropertyBase p) _ = p
projectProperty (PropertyComposite analysisShell vp1 vp2) c =  analysisShell (projectProperty vp1 c) (projectProperty vp2 c)

projectModel :: VarModel -> Conf -> Model
projectModel (ModelChoice o vm1 vm2) c = if c o then projectModel vm1 c else projectModel vm2 c
projectModel (ModelBase m) _ = m
projectModel (ModelComposite vm1 vm2) c = Composite (projectModel vm1 c)  (projectModel vm2 c)

analyzeModel :: Model -> Property
analyzeModel Basic = SomeValue
analyzeModel (Composite m1 m2) =  analyzeModelCompositeShell (analyzeModel  m1) (analyzeModel  m2)

varAnalyzeModel :: VarModel -> VarProperty
varAnalyzeModel (ModelBase m) = PropertyBase (analyzeModel m)
varAnalyzeModel (ModelChoice o vm1 vm2) = varJoinProperty o (varAnalyzeModel vm1) (varAnalyzeModel vm2)
varAnalyzeModel (ModelComposite vm1 vm2) = varCompositeProperty (varAnalyzeModel vm1) (varAnalyzeModel vm2)
