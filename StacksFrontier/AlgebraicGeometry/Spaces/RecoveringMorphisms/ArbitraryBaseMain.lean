module

public import StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.ArbitraryBaseStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.Main

/-!
# Recovering morphisms of algebraic spaces over an arbitrary base scheme

Let `X` and `Y` be algebraic spaces over a scheme `S` and let `(g, g♯)` be a morphism of locally
ringed topoi of their small étale ringed topoi whose chart morphisms are over `S`
(`AlgebraicGeometry.Space.IsChartOverBase`).  Then there is a unique morphism of algebraic spaces
`f : X ⟶ Y` over `S` with `(g, g♯)` 2-isomorphic to `(f_small, f♯)`. Over a terminal base the
condition holds by `AlgebraicGeometry.Space.isChartOverBase_of_isTerminal`.

## Main definitions

* `AlgebraicGeometry.Space.OverBase.recoveredHom`: the morphism of algebraic spaces recovered from
  `(g, g♯)`.

## Main results

* `AlgebraicGeometry.Space.existsUnique_spaceHom_twoIso_of_isChartOverBase`: existence and
  uniqueness of `f` with `(g, g♯) ≅ (f_small, f♯)` over an arbitrary base, for a `(g, g♯)` whose
  chart morphisms are over the base.
* `AlgebraicGeometry.Space.OverBase.nonempty_twoIso_recoveredHom`: `(g, g♯)` is 2-isomorphic to
  `(f_small, f♯)` for the recovered morphism `f`, under hypotheses on the stalks at the geometric
  points of `X`.

## Implementation notes

Over a general base the conclusion fails without `AlgebraicGeometry.Space.IsChartOverBase`: the
morphisms of algebraic spaces over `S` are required to commute with the structure morphisms to
`S`, which the topos-theoretic data do not see (for `S = X = Y = Spec L` and a nontrivial
automorphism `σ` of a field `L`, `(σ_small, σ♯)` is locally ringed and not 2-isomorphic to the
identity, while the identity is the only morphism over `S`).  It is exactly this counterexample
that `IsChartOverBase` excludes: there the chart morphisms are the `σ`-twists of the identity,
which are not morphisms over `L`.

## References

* [Stacks Project, Tag 04KL](https://stacks.math.columbia.edu/tag/04KL)
* [Stacks Project, Tag 04M6](https://stacks.math.columbia.edu/tag/04M6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

namespace OverBase

/-! ### The chart points of `g` -/

section Recovered

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS}
  {g : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y)}
  (hb : IsChartOverBase g)

attribute [local instance] smallEtaleTopology_subcanonical

/-- For an affine étale chart `V` of `Y`, the map of sheaves `g⁻¹h_V ⟶ Ŷ` sending a section `s`
over `U` to the composite `U ⟶ V ⟶ Y`, the first map being `f_s`. -/
def chartPointMap (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)] :
    invRep g V ⟶ chartPointSheaf X Y :=
  ⟨{ app U := ↾fun s ↦ Y.1.map (chartOverHom hb V U.unop s).op (yonedaEquiv V.obj.hom)
     naturality U U' i := by
      ext s
      change Y.1.map (chartOverHom hb V U'.unop ((invRep g V).obj.map i s)).op _ =
        Y.1.map i.unop.hom.left.op (Y.1.map (chartOverHom hb V U.unop s).op _)
      rw [show i = i.unop.op from rfl, chartOverHom_restrict, op_comp,
        FunctorToTypes.map_comp_apply]
      rfl }⟩

/-- The value of `g⁻¹h_V ⟶ Ŷ` at a section `s`: the composite of `f_s` with the chart `V`. -/
theorem chartPointMap_app (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)]
    (U : SmallEtale B S hS X.1) (s : (invRep g V).obj.obj (op U)) :
    (chartPointMap hb V).hom.app (op U) s =
      Y.1.map (chartOverHom hb V U s).op (yonedaEquiv V.obj.hom) :=
  rfl

/-- The maps `g⁻¹h_V ⟶ Ŷ` are natural in the affine chart `V`. -/
theorem map_comp_chartPointMap {V V' : SmallEtale B S hS Y.1} [IsAffine (chartSch V)]
    [IsAffine (chartSch V')] (c : V' ⟶ V) :
    g.toToposHom.inverseImage.map ((SmallEtale.topology B S hS Y.1).yoneda.map c) ≫
      chartPointMap hb V = chartPointMap hb V' := by
  apply Sheaf.hom_ext
  ext U s
  show Y.1.map (chartOverHom hb V U.unop ((g.toToposHom.inverseImage.map
      ((SmallEtale.topology B S hS Y.1).yoneda.map c)).hom.app (op U.unop) s)).op _ =
    Y.1.map (chartOverHom hb V' U.unop s).op _
  rw [chartOverHom_map, op_comp, FunctorToTypes.map_comp_apply, yonedaEquiv_naturality]
  congr 2
  exact CostructuredArrow.w c.hom

/-- The section of `g_*Ŷ` over an affine chart `V` of `Y` adjoint to `g⁻¹h_V ⟶ Ŷ`. -/
def chartPointSection (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)] :
    (g.toToposHom.pushforward.obj (chartPointSheaf X Y)).obj.obj (op V) :=
  (SmallEtale.topology B S hS Y.1).yonedaEquiv
    (g.toToposHom.adj.homEquiv _ _ (chartPointMap hb V))

/-- The sections of `g_*Ŷ` over the affine charts are compatible with restriction. -/
theorem chartPointSection_restrict {V V' : SmallEtale B S hS Y.1} [IsAffine (chartSch V)]
    [IsAffine (chartSch V')] (c : V' ⟶ V) :
    (g.toToposHom.pushforward.obj (chartPointSheaf X Y)).obj.map c.op
      (chartPointSection hb V) = chartPointSection hb V' := by
  rw [chartPointSection, GrothendieckTopology.yonedaEquiv_naturality,
    ← Adjunction.homEquiv_naturality_left, map_comp_chartPointMap]
  rfl

/-- The sections of `g_*Ŷ` over the affine charts of `Y`, as a map of presheaves on the affine
étale site out of the terminal presheaf. -/
def chartPointSectionsAffine :
    (AffineEtale.inclusion B S hS Y.1).op ⋙ (⊤_ Sheaf (SmallEtale.topology B S hS Y.1)
      (Type u)).obj ⟶
      (AffineEtale.inclusion B S hS Y.1).op ⋙
        (g.toToposHom.pushforward.obj (chartPointSheaf X Y)).obj where
  app V := ↾fun _ ↦
    haveI : IsAffine (chartSch V.unop.obj) := V.unop.property
    chartPointSection hb V.unop.obj
  naturality V V' c := by
    ext x
    have : IsAffine (chartSch V.unop.obj) := V.unop.property
    have : IsAffine (chartSch V'.unop.obj) := V'.unop.property
    exact (chartPointSection_restrict hb c.unop.hom).symm

/-- The global section of `g_*Ŷ` glued from the sections over the affine charts of `Y`. -/
def chartPointGlobalSection :
    ⊤_ Sheaf (SmallEtale.topology B S hS Y.1) (Type u) ⟶
      g.toToposHom.pushforward.obj (chartPointSheaf X Y) :=
  have := (AffineEtale.inclusion_isSpecialCocontinuous B S hS Y.1 Y.2).2
  have := Functor.IsDenseSubsite.isCoverDense (AffineEtale.topology B S hS Y.1)
    (SmallEtale.topology B S hS Y.1) (AffineEtale.inclusion B S hS Y.1)
  have := Functor.IsDenseSubsite.isLocallyFull (AffineEtale.topology B S hS Y.1)
    (SmallEtale.topology B S hS Y.1) (AffineEtale.inclusion B S hS Y.1)
  ⟨Functor.IsCoverDense.restrictHomEquivHom (chartPointSectionsAffine hb)⟩

/-- Over an affine chart, the glued global section is the section attached to that chart. -/
theorem chartPointGlobalSection_app (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)]
    (x : (⊤_ Sheaf (SmallEtale.topology B S hS Y.1) (Type u)).obj.obj (op V)) :
    (chartPointGlobalSection hb).hom.app (op V) x = chartPointSection hb V := by
  have := (AffineEtale.inclusion_isSpecialCocontinuous B S hS Y.1 Y.2).2
  have := Functor.IsDenseSubsite.isCoverDense (AffineEtale.topology B S hS Y.1)
    (SmallEtale.topology B S hS Y.1) (AffineEtale.inclusion B S hS Y.1)
  have := Functor.IsDenseSubsite.isLocallyFull (AffineEtale.topology B S hS Y.1)
    (SmallEtale.topology B S hS Y.1) (AffineEtale.inclusion B S hS Y.1)
  have h := congr_app ((Functor.IsCoverDense.restrictHomEquivHom
    (G := AffineEtale.inclusion B S hS Y.1)
    (ℱ' := g.toToposHom.pushforward.obj (chartPointSheaf X Y))).symm_apply_apply
      (chartPointSectionsAffine hb))
    (op (⟨V, (inferInstance : IsAffine (chartSch V))⟩ : AffineEtale B S hS Y.1))
  exact ConcreteCategory.congr_hom h x

/-- The map from the terminal sheaf to `Ŷ` adjoint to the glued global section. -/
def chartPointFamily : g.toToposHom.inverseImage.obj (⊤_ Sheaf (SmallEtale.topology B S hS Y.1)
    (Type u)) ⟶ chartPointSheaf X Y :=
  (g.toToposHom.adj.homEquiv _ _).symm (chartPointGlobalSection hb)

/-- **The point of `Y` over an étale chart `U` of `X` recovered from `g`.** -/
def recoveredPoint (U : SmallEtale B S hS X.1) : Y.1.obj (op U.obj.left) :=
  (chartPointFamily hb).hom.app (op U) default

/-- A map out of `g⁻¹` of the terminal sheaf takes the same value at any two sections. -/
private theorem hom_app_eq_of_inverseImage_terminal
    {F : Sheaf (SmallEtale.topology B S hS X.1) (Type u)}
    (φ : g.toToposHom.inverseImage.obj (⊤_ Sheaf (SmallEtale.topology B S hS Y.1) (Type u)) ⟶ F)
    (U : SmallEtale B S hS X.1)
    (a b : (g.toToposHom.inverseImage.obj
      (⊤_ Sheaf (SmallEtale.topology B S hS Y.1) (Type u))).obj.obj (op U)) :
    φ.hom.app (op U) a = φ.hom.app (op U) b :=
  congrArg _ (Subsingleton.elim _ _)

/-- The recovered points are compatible with the morphisms of charts. -/
theorem recoveredPoint_restrict {U U' : SmallEtale B S hS X.1} (i : U' ⟶ U) :
    Y.1.map i.hom.left.op (recoveredPoint hb U) = recoveredPoint hb U' :=
  (ConcreteCategory.congr_hom ((chartPointFamily hb).hom.naturality i.op) default).symm.trans
    (hom_app_eq_of_inverseImage_terminal (chartPointFamily hb) U' _ _)

/-- **The recovered point over `U` is the composite `U ⟶ V ⟶ Y` for every section `s` over
`U` of `g⁻¹h_V`**, `V` an affine étale chart of `Y`. -/
theorem recoveredPoint_eq (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)]
    (U : SmallEtale B S hS X.1) (s : (invRep g V).obj.obj (op U)) :
    recoveredPoint hb U = (chartPointMap hb V).hom.app (op U) s := by
  let k := terminal.from ((SmallEtale.topology B S hS Y.1).yoneda.obj V)
  have hk : k ≫ chartPointGlobalSection hb =
      g.toToposHom.adj.homEquiv _ _ (chartPointMap hb V) := by
    apply (SmallEtale.topology B S hS Y.1).yonedaEquiv.injective
    rw [GrothendieckTopology.yonedaEquiv_comp, chartPointGlobalSection_app]
    rfl
  have h : g.toToposHom.inverseImage.map k ≫ chartPointFamily hb = chartPointMap hb V := by
    rw [chartPointFamily, ← Adjunction.homEquiv_naturality_left_symm, hk,
      Equiv.symm_apply_apply]
  rw [← h]
  exact hom_app_eq_of_inverseImage_terminal _ _ _ _

/-- **The morphism of algebraic spaces recovered from `g`**: the descent of the recovered
points along the étale charts of `X`. -/
def recoveredHom : X ⟶ Y :=
  ObjectProperty.homMk (Classical.choose (exists_hom_of_chartFamily B S hS X.2 Y.2.isSheaf
    (recoveredPoint hb) (fun i ↦ recoveredPoint_restrict hb i)))

/-- The recovered morphism restricts on every étale chart `U` of `X` to the recovered point
over `U`. -/
theorem chart_comp_recoveredHom (U : SmallEtale B S hS X.1) :
    U.obj.hom ≫ (recoveredHom hb).hom = yonedaEquiv.symm (recoveredPoint hb U) :=
  Classical.choose_spec (exists_hom_of_chartFamily B S hS X.2 Y.2.isSheaf
    (recoveredPoint hb) (fun i ↦ recoveredPoint_restrict hb i)) U

/-- **The recovered morphism is compatible with every chart morphism `f_s`.** -/
theorem isChartCompatible_recoveredHom : IsChartCompatible hb (recoveredHom hb) := by
  intro V _ U s
  rw [chart_comp_recoveredHom, recoveredPoint_eq hb V U s, chartPointMap_app,
    yonedaEquiv_naturality, Equiv.symm_apply_apply]

/-- Every morphism of the small étale ringed topoi of two algebraic spaces whose chart morphisms
are over the base has a morphism of algebraic spaces compatible with all its chart morphisms
`f_s`. -/
theorem exists_isChartCompatible : ∃ f : X ⟶ Y, IsChartCompatible hb f :=
  ⟨recoveredHom hb, isChartCompatible_recoveredHom hb⟩

end Recovered

/-! ### The assembly -/

attribute [local instance] smallEtaleTopology_subcanonical

/-- A morphism of the small étale ringed topoi of two algebraic spaces whose chart morphisms are
over the base, whose stalk comparisons have the Hensel lifting property and its uniqueness, and for
which the stalks of the inverse images of representable sheaves lift to affine opens and do not all
vanish, is 2-isomorphic to `(f_small, f♯)` for the recovered morphism `f`. -/
theorem nonempty_twoIso_recoveredHom {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y : AlgebraicSpaces B S hS}
    {g : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y)}
    (hb : IsChartOverBase g)
    (hRS : ∀ (x : GeometricPoint B S hS X.1) {V₀ V' : SmallEtale B S hS Y.1}
      [IsAffine (chartSch V₀)] [IsAffine (chartSch V')] (c : V' ⟶ V₀),
      RelSurjAt x (isChartCompatible_recoveredHom hb) c)
    (hRI : ∀ (x : GeometricPoint B S hS X.1) {V₀ V' : SmallEtale B S hS Y.1}
      [IsAffine (chartSch V₀)] [IsAffine (chartSch V')] (c : V' ⟶ V₀),
      RelInjAt x (isChartCompatible_recoveredHom hb) c)
    (hT1 : ∀ (x : GeometricPoint B S hS X.1) (P : SmallEtale B S hS Y.1)
      (τ : (invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj P)),
      ∃ (O : ((BigFppfOver.toScheme B S hS).obj P.1.left).affineOpens)
        (τ' : (invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj
          (chartOpenRestriction B S hS Y.1 P O.1))),
        (invStalk g x).map ((SmallEtale.topology B S hS Y.1).yoneda.map
          (chartOpenRestrictionHom B S hS Y.1 P O.1)) τ' = τ)
    (hT6 : ∀ x : GeometricPoint B S hS X.1, ∃ (V₀ : SmallEtale B S hS Y.1)
      (_ : IsAffine (chartSch V₀)),
      Nonempty ((invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj V₀))) :
    Nonempty (RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u} g
      (smallEtaleRingedToposHom B S hS (recoveredHom hb))) :=
  ⟨twoIsoOfChartComparison (isChartCompatible_recoveredHom hb) fun V _ ↦
    W_invRepComparison_of_bijective (isChartCompatible_recoveredHom hb) V fun x ↦
      ⟨stalkComparison_injective x _ V (hRS x) (hRI x) (hT1 x),
        stalkComparison_surjective x _ V (hRS x) (hT6 x)⟩⟩

/-- The Hensel lifting property of the stalk comparison along every morphism of affine charts,
for a morphism of locally ringed topoi. -/
theorem relSurjAt_of_isLocallyRinged {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y : AlgebraicSpaces B S hS}
    {g : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y)}
    {hb : IsChartOverBase g}
    (hg : g.IsLocallyRinged) {f : X ⟶ Y} (hf : IsChartCompatible hb f)
    (x : GeometricPoint B S hS X.1) {V₀ V' : SmallEtale B S hS Y.1}
    [IsAffine (chartSch V₀)] [IsAffine (chartSch V')] (c : V' ⟶ V₀) :
    RelSurjAt x hf c := by
  obtain ⟨n, P, ⟨pres⟩, hP⟩ := Stacks.EtaleCohomology.exists_standardPresentationOver
    ((BigFppfOver.toScheme B S hS).map c.hom.left)
  exact fun σ₀ t' ht ↦ exists_stalk_lift hf x c pres (isLocalHom_invStalkRingHom g x hg)
    (fun ψ ↦ Algebra.Etale.quotient_span_range_map ψ P) σ₀ t' ht

/-- The uniqueness of the Hensel lift along every morphism of affine charts, for a morphism of
locally ringed topoi. -/
theorem relInjAt_of_isLocallyRinged {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y : AlgebraicSpaces B S hS}
    {g : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y)}
    {hb : IsChartOverBase g}
    (hg : g.IsLocallyRinged) {f : X ⟶ Y} (hf : IsChartCompatible hb f)
    (x : GeometricPoint B S hS X.1) {V₀ V' : SmallEtale B S hS Y.1}
    [IsAffine (chartSch V₀)] [IsAffine (chartSch V')] (c : V' ⟶ V₀) :
    RelInjAt x hf c := by
  obtain ⟨n, P, ⟨pres⟩, hP⟩ := Stacks.EtaleCohomology.exists_standardPresentationOver
    ((BigFppfOver.toScheme B S hS).map c.hom.left)
  exact fun σ' σ'' h₀ hc ↦ stalk_lift_unique hf x c pres (isLocalHom_invStalkRingHom g x hg)
    (fun ψ ↦ Algebra.Etale.quotient_span_range_map ψ P) σ' σ'' h₀ hc
end OverBase

attribute [local instance] smallEtaleTopology_subcanonical

/-- **The recovery of a morphism of algebraic spaces over an arbitrary base scheme.** Let `X` and
`Y` be algebraic spaces over a scheme `S` and let `(g, g♯)` be a morphism of locally ringed topoi
of their small étale ringed topoi whose chart morphisms are over `S`
(`AlgebraicGeometry.Space.IsChartOverBase`). Then there is a unique morphism of algebraic spaces
`f : X ⟶ Y` over `S` with `(g, g♯)` 2-isomorphic to `(f_small, f♯)`. -/
theorem existsUnique_spaceHom_twoIso_of_isChartOverBase {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}
    {g : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y)}
    (hb : IsChartOverBase g) (hg : g.IsLocallyRinged) :
    ∃! f : X ⟶ Y, Nonempty (RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u} g
      (smallEtaleRingedToposHom B S hS f)) := by
  have h := OverBase.nonempty_twoIso_recoveredHom hb
    (fun x _ _ _ _ c ↦ OverBase.relSurjAt_of_isLocallyRinged hg _ x c)
    (fun x _ _ _ _ c ↦ OverBase.relInjAt_of_isLocallyRinged hg _ x c)
    (fun x P τ ↦ exists_affineOpen_lift g x P τ) (fun x ↦ exists_affine_invStalk g x)
  refine ⟨OverBase.recoveredHom hb, h, fun f ⟨t⟩ ↦ ?_⟩
  obtain ⟨t'⟩ := h
  exact eq_of_twoIso_of_twoIso g f _ t t'

end AlgebraicGeometry.Space
