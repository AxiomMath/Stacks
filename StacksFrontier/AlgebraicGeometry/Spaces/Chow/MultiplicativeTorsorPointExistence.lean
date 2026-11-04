module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.MultiplicativeTorsorPointUniversal
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction

/-!
# Existence of points of the multiplicative torsor with prescribed trivialization

In Situation 0EDT let `X/B` be good, let `ℒ` be an invertible `𝒪_X`-module and let
`q : T ⟶ X` be its multiplicative torsor with `α : q^*ℒ ≅ 𝒪_T`.  This file proves that every
trivialization `β : x^*ℒ ≅ 𝒪_Z` along a morphism `x : Z ⟶ X` of algebraic spaces comes from a
point `t : Z ⟶ T` over `x`, and that this point is unique: `(T, α)` is the universal
trivialization of `ℒ`.

## References

* [Stacks Project, Tag 0EQG](https://stacks.math.columbia.edu/tag/0EQG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/-! ### Morphisms of modules are étale local -/

section EtaleLocality

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The étale chart `W` of an algebraic space `Z`, as a morphism of algebraic spaces from the
space represented by its source. -/
def chartInclusionHom {Z : AlgebraicSpaces B S hS} (W : SmallEtale B S hS Z.1) :
    representedAlgebraicSpace B S hS W.obj.left ⟶ Z :=
  ObjectProperty.homMk W.obj.hom

/-- The inclusion of an étale chart `W` of `Z` is étale. -/
theorem isEtale_chartInclusionHom {Z : AlgebraicSpaces B S hS} (W : SmallEtale B S hS Z.1) :
    IsEtale B S hS (chartInclusionHom B S hS W).hom :=
  (isEtale_iff_presheaf_of_yoneda B S hS _).2 W.property

/-- The chart of `Z` obtained by reading the identity chart of the source of a chart `W` as a
chart of `Z`, and its map to `W`. -/
def selfChartPostcompHom {Z : AlgebraicSpaces B S hS} (W : SmallEtale B S hS Z.1) :
    (smallEtalePostcomp B S hS (chartInclusionHom B S hS W)
      (isEtale_chartInclusionHom B S hS W)).obj (selfChart B S hS W.obj.left) ⟶ W :=
  ObjectProperty.homMk (CostructuredArrow.homMk (𝟙 _) (by
    change yoneda.map (𝟙 W.obj.left) ≫ W.obj.hom = 𝟙 _ ≫ W.obj.hom
    simp))

/-- **Two morphisms of modules on an algebraic space agree as soon as, around every point of
every chart, they agree after pullback to a chart.** -/
theorem modules_hom_ext_of_etaleRestriction {Z : AlgebraicSpaces B S hS}
    {M N : Modules.{u, u} B S hS Z.1 Z.2} (φ ψ : M ⟶ N)
    (h : ∀ (W : SmallEtale B S hS Z.1) (z : chartScheme W),
      ∃ (W' : SmallEtale B S hS Z.1) (a : W' ⟶ W),
        z ∈ Set.range ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS Z.1).map a)) ∧
          (modulePullback B S hS (chartInclusionHom B S hS W')).map φ =
            (modulePullback B S hS (chartInclusionHom B S hS W')).map ψ) :
    φ = ψ := by
  apply SheafOfModules.hom_ext
  refine PresheafOfModules.hom_ext fun W => ModuleCat.hom_ext (LinearMap.ext fun y => ?_)
  refine modules_eq_of_forall_point B S hS N W.unop _ _ fun z => ?_
  obtain ⟨W', a, hz, hφψ⟩ := h W.unop z
  let ι := chartInclusionHom B S hS W'
  let hι := isEtale_chartInclusionHom B S hS W'
  let E := modulePullbackIsoEtaleModulePullback B S hS ι hι
  have heq : (etaleModulePullback.{u, u} B S hS ι hι).map φ =
      (etaleModulePullback.{u, u} B S hS ι hι).map ψ :=
    (NatIso.naturality_1 E φ).symm.trans
      ((congrArg (fun χ => E.inv.app M ≫ χ ≫ E.hom.app N) hφψ).trans (NatIso.naturality_1 E ψ))
  have hP : ∀ s, φ.val.app (op ((smallEtalePostcomp B S hS ι hι).obj
      (selfChart B S hS W'.obj.left))) s = ψ.val.app (op ((smallEtalePostcomp B S hS ι hι).obj
      (selfChart B S hS W'.obj.left))) s := fun s =>
    congrArg (fun χ => χ.val.app (op (selfChart B S hS W'.obj.left)) s) heq
  refine ⟨_, selfChartPostcompHom B S hS W' ≫ a, ?_, ?_⟩
  · obtain ⟨w, rfl⟩ := hz
    exact ⟨w, rfl⟩
  · refine (PresheafOfModules.naturality_apply φ.val (selfChartPostcompHom B S hS W' ≫ a).op
      y).symm.trans (Eq.trans ?_ (PresheafOfModules.naturality_apply ψ.val
        (selfChartPostcompHom B S hS W' ≫ a).op y))
    exact hP _

/-- The morphism of represented algebraic spaces induced by a morphism of the site:
`AlgebraicGeometry.schemeSpaceMap`. -/
def representedAlgebraicSpaceMap {Y U : BigFppfOver B S hS} (f : Y ⟶ U) :
    representedAlgebraicSpace B S hS Y ⟶ representedAlgebraicSpace B S hS U :=
  schemeSpaceMap f

/-- The underlying morphism of presheaves of `representedAlgebraicSpaceMap f` is `yoneda.map f`. -/
theorem representedAlgebraicSpaceMap_hom {Y U : BigFppfOver B S hS} (f : Y ⟶ U) :
    (representedAlgebraicSpaceMap B S hS f).hom = yoneda.map f :=
  rfl

/-- `representedAlgebraicSpaceMap` is compatible with composition. -/
theorem representedAlgebraicSpaceMap_comp {Y' Y U : BigFppfOver B S hS} (g : Y' ⟶ Y) (f : Y ⟶ U) :
    representedAlgebraicSpaceMap B S hS (g ≫ f) =
      representedAlgebraicSpaceMap B S hS g ≫ representedAlgebraicSpaceMap B S hS f :=
  ObjectProperty.hom_ext _ (yoneda.map_comp g f)

/-- The morphism from a scheme to an algebraic space given by a point. -/
def representedHomOfPoint {Z : AlgebraicSpaces B S hS} {U : BigFppfOver B S hS}
    (z : Z.1.obj (op U)) :
    representedAlgebraicSpace B S hS U ⟶ Z :=
  ObjectProperty.homMk (yonedaEquiv.symm z)

/-- The underlying morphism of presheaves of the morphism given by a point `z` is the Yoneda
morphism of `z`. -/
theorem pointHom_hom {Z : AlgebraicSpaces B S hS} {U : BigFppfOver B S hS} (z : Z.1.obj (op U)) :
    (representedHomOfPoint B S hS z).hom = yonedaEquiv.symm z :=
  rfl

/-- The morphism given by the restriction of a point `z` along `g` is the morphism induced by `g`
followed by the morphism given by `z`. -/
theorem pointHom_map {Z : AlgebraicSpaces B S hS} {U U' : BigFppfOver B S hS} (g : U' ⟶ U)
    (z : Z.1.obj (op U)) :
    representedHomOfPoint B S hS (Z.1.map g.op z) =
      representedAlgebraicSpaceMap B S hS g ≫ representedHomOfPoint B S hS z :=
  ObjectProperty.hom_ext _ (yonedaEquiv_symm_map g.op z)

/-- Two morphisms of algebraic spaces agreeing after precomposition with every point agree. -/
private theorem hom_ext_of_forall_point {Z Y : AlgebraicSpaces B S hS} (a b : Z ⟶ Y)
    (h : ∀ (U : BigFppfOver B S hS) (z : Z.1.obj (op U)),
      representedHomOfPoint B S hS z ≫ a = representedHomOfPoint B S hS z ≫ b) : a = b := by
  apply ObjectProperty.hom_ext
  ext ⟨U⟩ z
  have := congrArg (fun φ => yonedaEquiv φ.hom) (h U z)
  simp only [pointHom_hom, ObjectProperty.FullSubcategory.comp_hom, yonedaEquiv_comp,
    Equiv.apply_symm_apply] at this
  exact this

end EtaleLocality

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1)
    (hL : IsInvertibleSheaf D p hp L)

/-! ### Points of `T` realizing a trivialization -/

section Lift

/-- The trivialization of `x^*ℒ` induced by a point `t` of `T` over `x`, written out; it refers
to the variables `D p hp L hL` in scope. -/
local macro "𝔱[" t:term ", " h:term "]" : term => do
  let D := Lean.mkIdent `D
  let p := Lean.mkIdent `p
  let hp := Lean.mkIdent `hp
  let L := Lean.mkIdent `L
  let hL := Lean.mkIdent `hL
  `((modulePullbackTriangle ($D).site ($D).base ($D).base_mem $h).hom.app $L ≫
    (((modulePullback ($D).site ($D).base ($D).base_mem $t).map
        (torsorOfInvertibleTrivialization $D $p $hp $L $hL).hom) ≫
      (modulePullbackUnitIso ($D).site ($D).base ($D).base_mem $t).hom))

/-- The restriction of a trivialization `β` along `g`, written out. -/
local macro "𝔯[" g:term ", " h:term ", " β:term "]" : term => do
  let D := Lean.mkIdent `D
  let L := Lean.mkIdent `L
  `((modulePullbackTriangle ($D).site ($D).base ($D).base_mem $h).hom.app $L ≫
    ((modulePullback ($D).site ($D).base ($D).base_mem $g).map $β ≫
      (modulePullbackUnitIso ($D).site ($D).base ($D).base_mem $g).hom))

/-- **Points realizing a trivialization restrict**: if `t` realizes `β`, then `g ≫ t` realizes
the restriction of `β` along `g`. -/
theorem torsorLift_comp {Z Z' : AlgebraicSpaces D.site D.base D.base_mem}
    {x : Z ⟶ (⟨X, hp.1⟩ : AlgebraicSpaces D.site D.base D.base_mem)}
    (β : (modulePullback D.site D.base D.base_mem x).obj L ⟶ SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite D.site D.base D.base_mem
        Z.1 Z.2).O))
    {t : Z ⟶ torsorOfInvertibleSpace D p hp L hL}
    (h : t ≫ torsorOfInvertibleProjection D p hp L hL = x) (hβ : 𝔱[t, h] = β)
    (g : Z' ⟶ Z) {x' : Z' ⟶ (⟨X, hp.1⟩ : AlgebraicSpaces D.site D.base D.base_mem)}
    (h' : g ≫ x = x') :
    ∃ hh : (g ≫ t) ≫ torsorOfInvertibleProjection D p hp L hL = x', 𝔱[g ≫ t, hh] = 𝔯[g, h', β] := by
  have hh : (g ≫ t) ≫ torsorOfInvertibleProjection D p hp L hL = x' := by
    rw [Category.assoc, h, h']
  refine ⟨hh, ?_⟩
  have N := modulePullbackTriangle_comp_unitIso D.site D.base D.base_mem g t
    (torsorOfInvertibleProjection D p hp L hL) L (torsorOfInvertibleTrivialization D p hp L hL).hom
    h h' hh
  exact N.trans (congrArg (fun χ => (modulePullbackTriangle D.site D.base D.base_mem h').hom.app L ≫
    ((modulePullback D.site D.base D.base_mem g).map χ ≫
      (modulePullbackUnitIso D.site D.base D.base_mem g).hom)) hβ)

/-- Restricting a trivialization twice is restricting it along the composite. -/
theorem restrict_restrict {Z Z' Z'' : AlgebraicSpaces D.site D.base D.base_mem}
    {x : Z ⟶ (⟨X, hp.1⟩ : AlgebraicSpaces D.site D.base D.base_mem)}
    (β : (modulePullback D.site D.base D.base_mem x).obj L ⟶ SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite D.site D.base D.base_mem
        Z.1 Z.2).O))
    (g : Z' ⟶ Z) {x' : Z' ⟶ (⟨X, hp.1⟩ : AlgebraicSpaces D.site D.base D.base_mem)}
    (h : g ≫ x = x') (g' : Z'' ⟶ Z')
    {x'' : Z'' ⟶ (⟨X, hp.1⟩ : AlgebraicSpaces D.site D.base D.base_mem)}
    (h' : g' ≫ x' = x'') (hh : (g' ≫ g) ≫ x = x'') :
    𝔯[g', h', 𝔯[g, h, β]] = 𝔯[g' ≫ g, hh, β] :=
  (modulePullbackTriangle_comp_unitIso D.site D.base D.base_mem g' g x L β h h' hh).symm

/-- **A point of `T` over `x` whose restriction along `g` realizes the restriction of `β`
induces a trivialization agreeing with `β` after pullback along `g`.** -/
theorem modulePullback_map_eq_of_torsorLift_comp {Z Z' : AlgebraicSpaces D.site D.base D.base_mem}
    {x : Z ⟶ (⟨X, hp.1⟩ : AlgebraicSpaces D.site D.base D.base_mem)}
    (β : (modulePullback D.site D.base D.base_mem x).obj L ⟶ SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite D.site D.base D.base_mem
        Z.1 Z.2).O))
    (t : Z ⟶ torsorOfInvertibleSpace D p hp L hL)
    (h : t ≫ torsorOfInvertibleProjection D p hp L hL = x) (g : Z' ⟶ Z)
    (hh : (g ≫ t) ≫ torsorOfInvertibleProjection D p hp L hL = g ≫ x)
    (hg : 𝔱[g ≫ t, hh] = 𝔯[g, (rfl : g ≫ x = g ≫ x), β]) :
    (modulePullback D.site D.base D.base_mem g).map 𝔱[t, h] =
      (modulePullback D.site D.base D.base_mem g).map β := by
  have N := modulePullbackTriangle_comp_unitIso D.site D.base D.base_mem g t
    (torsorOfInvertibleProjection D p hp L hL) L (torsorOfInvertibleTrivialization D p hp L hL).hom
    h rfl hh
  exact (Iso.cancel_iso_hom_right _ _ (modulePullbackUnitIso D.site D.base D.base_mem g)).1
    ((Iso.cancel_iso_hom_left ((modulePullbackTriangle D.site D.base D.base_mem
      (rfl : g ≫ x = g ≫ x)).app L) _ _).1 (N.symm.trans hg))

/-- The restrictions of a trivialization `β` along two equal morphisms agree. -/
theorem restrict_congr {Z Z' : AlgebraicSpaces D.site D.base D.base_mem}
    {x : Z ⟶ (⟨X, hp.1⟩ : AlgebraicSpaces D.site D.base D.base_mem)}
    (β : (modulePullback D.site D.base D.base_mem x).obj L ⟶ SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite D.site D.base D.base_mem
        Z.1 Z.2).O))
    {g₁ g₂ : Z' ⟶ Z} (hg : g₁ = g₂)
    {x' : Z' ⟶ (⟨X, hp.1⟩ : AlgebraicSpaces D.site D.base D.base_mem)}
    (h₁ : g₁ ≫ x = x') (h₂ : g₂ ≫ x = x') : 𝔯[g₁, h₁, β] = 𝔯[g₂, h₂, β] := by
  subst hg
  cases proof_irrel h₁ h₂
  rfl

/-- Two equal points of `T` over `x` induce the same trivialization of `x^*ℒ`. -/
theorem triv_congr {Z : AlgebraicSpaces D.site D.base D.base_mem}
    {x : Z ⟶ (⟨X, hp.1⟩ : AlgebraicSpaces D.site D.base D.base_mem)}
    {t₁ t₂ : Z ⟶ torsorOfInvertibleSpace D p hp L hL} (ht : t₁ = t₂)
    (h₁ : t₁ ≫ torsorOfInvertibleProjection D p hp L hL = x)
    (h₂ : t₂ ≫ torsorOfInvertibleProjection D p hp L hL = x) : 𝔱[t₁, h₁] = 𝔱[t₂, h₂] := by
  subst ht
  cases proof_irrel h₁ h₂
  rfl

/-- The morphism of represented algebraic spaces induced by a morphism of the site. -/
local macro "ρ[" f:term "]" : term => do
  let D := Lean.mkIdent `D
  `(representedAlgebraicSpaceMap ($D).site ($D).base ($D).base_mem $f)

/-- **A trivialization of `x^*ℒ` lifts over the source chart of a chart diagram trivializing
`ℒ`.** -/
theorem exists_torsorLift_chartDiagram {U : BigFppfOver D.site D.base D.base_mem}
    (x : representedAlgebraicSpace D.site D.base D.base_mem U ⟶
      (⟨X, hp.1⟩ : AlgebraicSpaces D.site D.base D.base_mem))
    (β : (modulePullback D.site D.base D.base_mem x).obj L ≅ SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite D.site D.base D.base_mem
        (representedAlgebraicSpace D.site D.base D.base_mem U).1
        (representedAlgebraicSpace D.site D.base D.base_mem U).2).O))
    (d : ChartDiagram D.site D.base D.base_mem
      (representedAlgebraicSpace D.site D.base D.base_mem U).1 X x.hom)
    [IsAffine (chartScheme d.V)]
    (e : L.over d.V ≅ SheafOfModules.unit ((tensorStructureSheaf D p hp).over d.V))
    (k : representedAlgebraicSpace D.site D.base D.base_mem d.U.obj.left ⟶
      representedAlgebraicSpace D.site D.base D.base_mem U)
    (hk : chartDiagramSourceInclusion D p hp x d = k) :
    ∃ (t : representedAlgebraicSpace D.site D.base D.base_mem d.U.obj.left ⟶
        torsorOfInvertibleSpace D p hp L hL)
      (h : t ≫ torsorOfInvertibleProjection D p hp L hL = k ≫ x),
      𝔱[t, h] = 𝔯[k, (rfl : k ≫ x = k ≫ x), β.hom] := by
  subst hk
  have E := localTorsorHom_trivialization D p hp L hL x β d e
  have E2 : (restrictedTrivialization D p hp L x β d).hom =
      𝔯[chartDiagramSourceInclusion D p hp x d,
        (rfl : chartDiagramSourceInclusion D p hp x d ≫ x =
          chartDiagramSourceInclusion D p hp x d ≫ x), β.hom] := by
    refine (congrArg Iso.hom (restrictedTrivialization_eq D p hp L x β d)).trans ?_
    rw [modulePullbackRestrictIso_hom, modulePullbackTriangle_rfl, Iso.symm_hom]
  exact ⟨localTorsorHom D p hp L hL x β d e, localTorsorHom_comp D p hp L hL x β d e, E.trans E2⟩

/-- **The predicate "lifts over `f`" is stable under restriction.** -/
theorem torsorLift_repMap_comp {U Y Y' : BigFppfOver D.site D.base D.base_mem}
    (x : representedAlgebraicSpace D.site D.base D.base_mem U ⟶
      (⟨X, hp.1⟩ : AlgebraicSpaces D.site D.base D.base_mem))
    (β : (modulePullback D.site D.base D.base_mem x).obj L ⟶ SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite D.site D.base D.base_mem
        (representedAlgebraicSpace D.site D.base D.base_mem U).1
        (representedAlgebraicSpace D.site D.base D.base_mem U).2).O))
    (f : Y ⟶ U) (t : representedAlgebraicSpace D.site D.base D.base_mem Y ⟶
      torsorOfInvertibleSpace D p hp L hL)
    (h : t ≫ torsorOfInvertibleProjection D p hp L hL = ρ[f] ≫ x)
    (ht : 𝔱[t, h] = 𝔯[ρ[f], (rfl : ρ[f] ≫ x = ρ[f] ≫ x), β]) (g : Y' ⟶ Y) :
    ∃ hh : (ρ[g] ≫ t) ≫ torsorOfInvertibleProjection D p hp L hL = ρ[g ≫ f] ≫ x,
      𝔱[ρ[g] ≫ t, hh] = 𝔯[ρ[g ≫ f], (rfl : ρ[g ≫ f] ≫ x = ρ[g ≫ f] ≫ x), β] := by
  have hc : ρ[g ≫ f] = ρ[g] ≫ ρ[f] := representedAlgebraicSpaceMap_comp D.site D.base D.base_mem g f
  have h' : ρ[g] ≫ (ρ[f] ≫ x) = ρ[g ≫ f] ≫ x := by rw [hc, Category.assoc]
  have h3 : (ρ[g] ≫ ρ[f]) ≫ x = ρ[g ≫ f] ≫ x := by rw [← hc]
  obtain ⟨hh, e⟩ := torsorLift_comp D p hp L hL _ h ht ρ[g] h'
  have e2 := restrict_restrict D p hp L β ρ[f] (rfl : ρ[f] ≫ x = ρ[f] ≫ x) ρ[g] h' h3
  have e3 := restrict_congr D p hp L β hc.symm h3 (rfl : ρ[g ≫ f] ≫ x = ρ[g ≫ f] ≫ x)
  exact ⟨hh, e.trans (e2.trans e3)⟩

/-- **Gluing points of an algebraic space over a covering sieve of a scheme.** -/
theorem exists_hom_of_sieve {Tsp : AlgebraicSpaces D.site D.base D.base_mem}
    {U : BigFppfOver D.site D.base D.base_mem} (S : Sieve U)
    (hS : S ∈ BigFppfOver.topology D.site D.base D.base_mem U)
    (tf : ∀ ⦃Y : BigFppfOver D.site D.base D.base_mem⦄ (f : Y ⟶ U), S f →
      (representedAlgebraicSpace D.site D.base D.base_mem Y ⟶ Tsp))
    (hc : ∀ ⦃Y Y' : BigFppfOver D.site D.base D.base_mem⦄ (f : Y ⟶ U) (hf : S f) (g : Y' ⟶ Y),
      tf (g ≫ f) (S.downward_closed hf g) = ρ[g] ≫ tf f hf) :
    ∃ t : representedAlgebraicSpace D.site D.base D.base_mem U ⟶ Tsp,
      ∀ ⦃Y : BigFppfOver D.site D.base D.base_mem⦄ (f : Y ⟶ U) (hf : S f), ρ[f] ≫ t = tf f hf := by
  let fam : Presieve.FamilyOfElements Tsp.1 S.arrows := fun Y f hf => yonedaEquiv (tf f hf).hom
  have hfam : fam.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro Y Y' f g hf
    show yonedaEquiv (tf (g ≫ f) _).hom = Tsp.1.map g.op (yonedaEquiv (tf f hf).hom)
    rw [yonedaEquiv_naturality, hc f hf g]
    rfl
  obtain ⟨s, hs, -⟩ := (isSheaf_iff_isSheaf_of_type _ _).1 Tsp.property.isSheaf S hS fam hfam
  refine ⟨ObjectProperty.homMk (yonedaEquiv.symm s), fun Y f hf => ?_⟩
  refine ObjectProperty.hom_ext _ (yonedaEquiv.injective ?_)
  show yonedaEquiv (yoneda.map f ≫ yonedaEquiv.symm s) = yonedaEquiv (tf f hf).hom
  rw [← yonedaEquiv_naturality, Equiv.apply_symm_apply]
  exact hs f hf

/-- **Morphisms from a scheme to an algebraic space agreeing on a covering sieve agree.** -/
theorem representedHom_ext_of_sieve {Tsp : AlgebraicSpaces D.site D.base D.base_mem}
    {U : BigFppfOver D.site D.base D.base_mem} (S : Sieve U)
    (hS : S ∈ BigFppfOver.topology D.site D.base D.base_mem U)
    (a b : representedAlgebraicSpace D.site D.base D.base_mem U ⟶ Tsp)
    (h : ∀ ⦃Y : BigFppfOver D.site D.base D.base_mem⦄ (f : Y ⟶ U), S f → ρ[f] ≫ a = ρ[f] ≫ b) :
    a = b := by
  have hsep := ((isSheaf_iff_isSheaf_of_type _ _).1 Tsp.property.isSheaf S hS).isSeparatedFor
  refine ObjectProperty.hom_ext _ (yonedaEquiv.injective (hsep.ext fun Y f hf => ?_))
  rw [yonedaEquiv_naturality, yonedaEquiv_naturality]
  exact congrArg (fun φ => yonedaEquiv φ.hom) (h f hf)

include hL in
/-- **A sieve containing the source charts of all chart diagrams over `x` with affine chart
trivializing `ℒ` is covering.** -/
theorem mem_topology_of_chartDiagrams {U : BigFppfOver D.site D.base D.base_mem}
    (x : representedAlgebraicSpace D.site D.base D.base_mem U ⟶
      (⟨X, hp.1⟩ : AlgebraicSpaces D.site D.base D.base_mem)) (S : Sieve U)
    (hS : ∀ (d : ChartDiagram D.site D.base D.base_mem
      (representedAlgebraicSpace D.site D.base D.base_mem U).1 X x.hom),
      IsAffine (chartScheme d.V) →
      Nonempty (L.over d.V ≅ SheafOfModules.unit ((tensorStructureSheaf D p hp).over d.V)) →
        ∀ f : d.U.obj.left ⟶ U, yoneda.map f = d.U.obj.hom → S f) :
    S ∈ BigFppfOver.topology D.site D.base D.base_mem U := by
  choose d k haff he hz using fun z => exists_trivial_affine_chartDiagram_at_point D p hp L hL
    x (selfChart D.site D.base D.base_mem U) z
  let f : ∀ z, (d z).U.obj.left ⟶ U := fun z =>
    (SmallEtale.toOver D.site D.base D.base_mem _).map (k z)
  have hcov : Sieve.generate (Presieve.ofArrows (fun z => (d z).U.obj.left) f) ∈
      BigFppfOver.topology D.site D.base D.base_mem U :=
    BigFppfOver.sieve_generate_ofArrows_mem_topology _ f
      ((Scheme.ofArrows_mem_precoverage_iff (P := @Flat ⊓ @LocallyOfFinitePresentation)).mpr
        ⟨fun x => ⟨x, hz x⟩, fun z => by
          have : Etale ((BigFppfOver.toScheme D.site D.base D.base_mem).map (f z)) :=
            etale_toScheme_toOver_map D.site D.base D.base_mem _ (k z)
          exact ⟨inferInstance, inferInstance⟩⟩)
  refine GrothendieckTopology.superset_covering _ ?_ hcov
  rw [Sieve.generate_le_iff]
  rintro _ _ ⟨z⟩
  exact hS (d z) (haff z) (he z) (f z) ((Category.comp_id _).symm.trans
    ((SmallEtale.inclusion D.site D.base D.base_mem _).map (k z)).w)

include hL in
/-- **A point of `T` over `x` whose restrictions to the charts trivializing `ℒ` realize the
restrictions of `β` realizes `β`.** -/
theorem torsorTrivialization_eq_of_chartDiagrams {U : BigFppfOver D.site D.base D.base_mem}
    (x : representedAlgebraicSpace D.site D.base D.base_mem U ⟶
      (⟨X, hp.1⟩ : AlgebraicSpaces D.site D.base D.base_mem))
    (β : (modulePullback D.site D.base D.base_mem x).obj L ⟶ SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite D.site D.base D.base_mem
        (representedAlgebraicSpace D.site D.base D.base_mem U).1
        (representedAlgebraicSpace D.site D.base D.base_mem U).2).O))
    (t : representedAlgebraicSpace D.site D.base D.base_mem U ⟶
      torsorOfInvertibleSpace D p hp L hL)
    (ha : t ≫ torsorOfInvertibleProjection D p hp L hL = x)
    (hloc : ∀ (d : ChartDiagram D.site D.base D.base_mem
        (representedAlgebraicSpace D.site D.base D.base_mem U).1 X x.hom),
      IsAffine (chartScheme d.V) →
      Nonempty (L.over d.V ≅ SheafOfModules.unit ((tensorStructureSheaf D p hp).over d.V)) →
        ∀ (f : d.U.obj.left ⟶ U) (hh : (ρ[f] ≫ t) ≫ torsorOfInvertibleProjection D p hp L hL =
          ρ[f] ≫ x), yoneda.map f = d.U.obj.hom →
          𝔱[ρ[f] ≫ t, hh] = 𝔯[ρ[f], (rfl : ρ[f] ≫ x = ρ[f] ≫ x), β]) :
    𝔱[t, ha] = β := by
  refine modules_hom_ext_of_etaleRestriction D.site D.base D.base_mem _ _ fun W w => ?_
  obtain ⟨d', k', haff', he', hz'⟩ := exists_trivial_affine_chartDiagram_at_point D p hp L hL x W w
  refine ⟨d'.U, k', hz', ?_⟩
  have hf'w : yoneda.map (Yoneda.fullyFaithful.preimage d'.U.obj.hom) = d'.U.obj.hom :=
    Yoneda.fullyFaithful.map_preimage _
  have hι : chartInclusionHom D.site D.base D.base_mem d'.U =
      ρ[Yoneda.fullyFaithful.preimage d'.U.obj.hom] := ObjectProperty.hom_ext _ hf'w.symm
  have hh : (ρ[Yoneda.fullyFaithful.preimage d'.U.obj.hom] ≫ t) ≫
      torsorOfInvertibleProjection D p hp L hL =
        ρ[Yoneda.fullyFaithful.preimage d'.U.obj.hom] ≫ x := by
    rw [Category.assoc, ha]
  rw [hι]
  exact modulePullback_map_eq_of_torsorLift_comp D p hp L hL β t ha
    ρ[Yoneda.fullyFaithful.preimage d'.U.obj.hom] hh (hloc d' haff' he' _ hh hf'w)

/-- **Existence in the universal property of `(T, α)`, over schemes**: every trivialization
`β : x^*ℒ ≅ 𝒪_U` along a morphism `x : U ⟶ X` from a scheme is induced by a point of `T` over
`x`. -/
theorem exists_torsorLift_of_represented {U : BigFppfOver D.site D.base D.base_mem}
    (x : representedAlgebraicSpace D.site D.base D.base_mem U ⟶
      (⟨X, hp.1⟩ : AlgebraicSpaces D.site D.base D.base_mem))
    (β : (modulePullback D.site D.base D.base_mem x).obj L ≅ SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite D.site D.base D.base_mem
        (representedAlgebraicSpace D.site D.base D.base_mem U).1
        (representedAlgebraicSpace D.site D.base D.base_mem U).2).O)) :
    ∃ (t : representedAlgebraicSpace D.site D.base D.base_mem U ⟶
        torsorOfInvertibleSpace D p hp L hL)
      (h : t ≫ torsorOfInvertibleProjection D p hp L hL = x), 𝔱[t, h] = β.hom := by
  let S : Sieve U :=
    { arrows := fun Y f => ∃ (t : representedAlgebraicSpace D.site D.base D.base_mem Y ⟶
          torsorOfInvertibleSpace D p hp L hL)
        (h : t ≫ torsorOfInvertibleProjection D p hp L hL = ρ[f] ≫ x),
          𝔱[t, h] = 𝔯[ρ[f], (rfl : ρ[f] ≫ x = ρ[f] ≫ x), β.hom]
      downward_closed := by
        rintro Y Y' f ⟨t, h, ht⟩ g
        obtain ⟨hh, e⟩ := torsorLift_repMap_comp D p hp L hL x β.hom f t h ht g
        exact ⟨_, hh, e⟩ }
  have hS : S ∈ BigFppfOver.topology D.site D.base D.base_mem U :=
    mem_topology_of_chartDiagrams D p hp L hL x S (fun d hd he f hf => by
      have := hd
      exact exists_torsorLift_chartDiagram D p hp L hL x β d he.some ρ[f]
        (ObjectProperty.hom_ext _ hf.symm))
  obtain ⟨t, ht⟩ := exists_hom_of_sieve D S hS (fun Y f hf => hf.choose)
    (fun Y Y' f hf g => by
      obtain ⟨hh, e⟩ := torsorLift_repMap_comp D p hp L hL x β.hom f _
        hf.choose_spec.choose hf.choose_spec.choose_spec g
      exact torsorHom_eq_of_trivialization D p hp L hL _ _
        (S.downward_closed hf g).choose_spec.choose hh
        ((S.downward_closed hf g).choose_spec.choose_spec.trans e.symm))
  have ha : t ≫ torsorOfInvertibleProjection D p hp L hL = x :=
    representedHom_ext_of_sieve D S hS _ _ (fun Y f hf => by
      rw [← Category.assoc, ht f hf]
      exact hf.choose_spec.choose)
  refine ⟨t, ha, torsorTrivialization_eq_of_chartDiagrams D p hp L hL x β.hom t ha
    (fun d hd he f hh hf => ?_)⟩
  have := hd
  have hf' : S.arrows f := exists_torsorLift_chartDiagram D p hp L hL x β d he.some _
    (ObjectProperty.hom_ext _ hf.symm)
  exact (triv_congr D p hp L hL (ht _ hf') hh hf'.choose_spec.choose).trans
    hf'.choose_spec.choose_spec

/-- **Restricting a point realizing the restriction of `β` along `k`.** -/
theorem torsorLift_restrict {Z Z₁ Z₂ : AlgebraicSpaces D.site D.base D.base_mem}
    (x : Z ⟶ (⟨X, hp.1⟩ : AlgebraicSpaces D.site D.base D.base_mem))
    (β : (modulePullback D.site D.base D.base_mem x).obj L ⟶ SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite D.site D.base D.base_mem
        Z.1 Z.2).O))
    (k : Z₁ ⟶ Z) (t : Z₁ ⟶ torsorOfInvertibleSpace D p hp L hL)
    (h : t ≫ torsorOfInvertibleProjection D p hp L hL = k ≫ x)
    (ht : 𝔱[t, h] = 𝔯[k, (rfl : k ≫ x = k ≫ x), β]) (g : Z₂ ⟶ Z₁) (k' : Z₂ ⟶ Z)
    (hk : g ≫ k = k') :
    ∃ hh : (g ≫ t) ≫ torsorOfInvertibleProjection D p hp L hL = k' ≫ x,
      𝔱[g ≫ t, hh] = 𝔯[k', (rfl : k' ≫ x = k' ≫ x), β] := by
  subst hk
  have h' : g ≫ (k ≫ x) = (g ≫ k) ≫ x := (Category.assoc _ _ _).symm
  obtain ⟨hh, e⟩ := torsorLift_comp D p hp L hL _ h ht g h'
  exact ⟨hh, e.trans (restrict_restrict D p hp L β k rfl g h' rfl)⟩

/-- **Uniqueness in the universal property of `(T, α)`**: two points of `T` over the same
point of `X` inducing the same trivialization are equal. -/
theorem torsorHom_eq_of_trivialization_eq {Z : AlgebraicSpaces D.site D.base D.base_mem}
    {x : Z ⟶ (⟨X, hp.1⟩ : AlgebraicSpaces D.site D.base D.base_mem)}
    (t t' : Z ⟶ torsorOfInvertibleSpace D p hp L hL)
    (h : t ≫ torsorOfInvertibleProjection D p hp L hL = x)
    (h' : t' ≫ torsorOfInvertibleProjection D p hp L hL = x) (hβ : 𝔱[t, h] = 𝔱[t', h']) :
    t = t' := by
  refine hom_ext_of_forall_point D.site D.base D.base_mem _ _ fun U z => ?_
  let k := representedHomOfPoint D.site D.base D.base_mem (Z := Z) z
  obtain ⟨hh, e⟩ := torsorLift_comp D p hp L hL _ h hβ k (rfl : k ≫ x = k ≫ x)
  obtain ⟨hh', e'⟩ := torsorLift_comp D p hp L hL _ h' rfl k (rfl : k ≫ x = k ≫ x)
  exact torsorHom_eq_of_trivialization D p hp L hL (k ≫ t) (k ≫ t') hh hh' (e.trans e'.symm)

/-- **Existence in the universal property of `(T, α)`**: every trivialization
`β : x^*ℒ ≅ 𝒪_Z` along a morphism `x : Z ⟶ X` of algebraic spaces is induced by a point of `T`
over `x`. -/
theorem exists_torsorLift {Z : AlgebraicSpaces D.site D.base D.base_mem}
    (x : Z ⟶ (⟨X, hp.1⟩ : AlgebraicSpaces D.site D.base D.base_mem))
    (β : (modulePullback D.site D.base D.base_mem x).obj L ≅ SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite D.site D.base D.base_mem
        Z.1 Z.2).O)) :
    ∃ (t : Z ⟶ torsorOfInvertibleSpace D p hp L hL)
      (h : t ≫ torsorOfInvertibleProjection D p hp L hL = x), 𝔱[t, h] = β.hom := by
  have hpt : ∀ (U : BigFppfOver D.site D.base D.base_mem) (z : Z.1.obj (op U)),
      ∃ (tz : representedAlgebraicSpace D.site D.base D.base_mem U ⟶
          torsorOfInvertibleSpace D p hp L hL)
        (h : tz ≫ torsorOfInvertibleProjection D p hp L hL =
          representedHomOfPoint D.site D.base D.base_mem z ≫ x),
        𝔱[tz, h] = 𝔯[representedHomOfPoint D.site D.base D.base_mem z,
          (rfl : representedHomOfPoint D.site D.base D.base_mem z ≫ x =
            representedHomOfPoint D.site D.base D.base_mem z ≫ x),
          β.hom] := by
    intro U z
    obtain ⟨tz, h, e⟩ := exists_torsorLift_of_represented D p hp L hL
      (representedHomOfPoint D.site D.base D.base_mem z ≫ x)
      (modulePullbackRestrictIso D.site D.base D.base_mem
        (representedHomOfPoint D.site D.base D.base_mem z) x L β)
    refine ⟨tz, h, e.trans ?_⟩
    rw [modulePullbackRestrictIso_hom, modulePullbackTriangle_rfl, Iso.symm_hom]
  obtain ⟨tz, hspec⟩ := Classical.skolem.mp (fun U => Classical.skolem.mp (hpt U))
  have hnat : ∀ (U U' : BigFppfOver D.site D.base D.base_mem) (g : U' ⟶ U) (z : Z.1.obj (op U)),
      tz U' (Z.1.map g.op z) = ρ[g] ≫ tz U z := by
    intro U U' g z
    obtain ⟨h₁, e₁⟩ := hspec U z
    obtain ⟨h₂, e₂⟩ := hspec U' (Z.1.map g.op z)
    obtain ⟨hh, e⟩ := torsorLift_restrict D p hp L hL x β.hom
      (representedHomOfPoint D.site D.base D.base_mem z) (tz U z) h₁ e₁ ρ[g]
      (representedHomOfPoint D.site D.base D.base_mem (Z.1.map g.op z))
      (pointHom_map D.site D.base D.base_mem g z).symm
    exact torsorHom_eq_of_trivialization D p hp L hL _ _ h₂ hh (e₂.trans e.symm)
  obtain ⟨t, htpt⟩ : ∃ t : Z ⟶ torsorOfInvertibleSpace D p hp L hL,
      ∀ (U : BigFppfOver D.site D.base D.base_mem) (z : Z.1.obj (op U)),
        representedHomOfPoint D.site D.base D.base_mem z ≫ t = tz U z := by
    refine ⟨ObjectProperty.homMk
      { app := fun U => TypeCat.ofHom fun z => yonedaEquiv (tz U.unop z).hom
        naturality := fun U U' g => by
          ext z
          show yonedaEquiv (tz U'.unop (Z.1.map g.unop.op z)).hom =
            (torsorOfInvertibleSpace D p hp L hL).1.map g.unop.op (yonedaEquiv (tz U.unop z).hom)
          rw [hnat U.unop U'.unop g.unop z, yonedaEquiv_naturality]
          rfl }, fun U z => ?_⟩
    refine ObjectProperty.hom_ext _ (yonedaEquiv.injective ?_)
    rw [ObjectProperty.FullSubcategory.comp_hom, yonedaEquiv_comp, pointHom_hom,
      Equiv.apply_symm_apply]
    exact TypeCat.ofHom_apply _ _
  have ha : t ≫ torsorOfInvertibleProjection D p hp L hL = x := by
    refine hom_ext_of_forall_point D.site D.base D.base_mem _ _ fun U z => ?_
    obtain ⟨h₁, -⟩ := hspec U z
    rwa [← htpt U z, Category.assoc] at h₁
  refine ⟨t, ha, ?_⟩
  refine modules_hom_ext_of_etaleRestriction D.site D.base D.base_mem _ _ fun W w =>
    ⟨W, 𝟙 W, ⟨w, rfl⟩, ?_⟩
  have hg : chartInclusionHom D.site D.base D.base_mem W =
      representedHomOfPoint D.site D.base D.base_mem (Z := Z) (yonedaEquiv W.obj.hom) :=
    ObjectProperty.hom_ext _ (Equiv.symm_apply_apply _ _).symm
  rw [hg]
  have hh : (representedHomOfPoint D.site D.base D.base_mem (Z := Z) (yonedaEquiv W.obj.hom) ≫ t) ≫
      torsorOfInvertibleProjection D p hp L hL =
        representedHomOfPoint D.site D.base D.base_mem (Z := Z) (yonedaEquiv W.obj.hom) ≫ x := by
    rw [Category.assoc, ha]
  obtain ⟨h₁, e₁⟩ := hspec _ (yonedaEquiv W.obj.hom)
  exact modulePullback_map_eq_of_torsorLift_comp D p hp L hL β.hom t ha _ hh
    ((triv_congr D p hp L hL (htpt _ _) hh h₁).trans e₁)

end Lift

end AlgebraicGeometry.Space

end
