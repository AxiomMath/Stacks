module

public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.BaseChange
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.StandardShrinking
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.OneStep.Shrinking

/-!
# Restricting one stage of a complete dévissage to standard opens

A standard shrinking of the one-step dévissage underlying a stage of a complete dévissage
produces a stage of a complete dévissage again, provided the square formed by the finite
morphisms of the two one-step dévissages is cartesian: the free-module map of the restricted
stage is then the inverse image of the original one, and the restricted stage is a standard
restriction of the original one in the sense of Stacks 05HL.

## Main definitions

* `AlgebraicGeometry.OneStepDevissage.ShrinkingOpens`: the four standard opens of a shrinking,
  with the two opens of the closed subscheme and of the smooth scheme cut out exactly by the
  opens below them, together with surjectivity of the restricted smooth morphism.

## Main results

* `AlgebraicGeometry.map_fiberι_genericPoint_of_isOpenImmersion`: in a commuting square of two
  open immersions over a morphism with geometrically irreducible fibres, the generic point of a
  fibre is carried to the generic point of the corresponding fibre.
* `AlgebraicGeometry.cokernelIsoOfStageIsStandardRestriction`: the cokernel of the free-module
  map of a standard restriction is the restriction of the cokernel of the original one.
* `AlgebraicGeometry.exists_stageIsStandardRestriction_of_standardShrinking`: a standard
  shrinking with cartesian square of finite morphisms realises a stage as a standard
  restriction of another.
* `AlgebraicGeometry.exists_shrinkingOpens_smooth`: a prescribed standard open neighbourhood of
  the distinguished point of the smooth scheme occurs, cut down to a standard open of the base,
  as the smooth open of a shrinking of the above kind.
* `AlgebraicGeometry.exists_shrinkingOpens_smooth_inside`: the same, with the source open of the
  shrinking in addition contained in a prescribed standard open neighbourhood of `x`.
* `AlgebraicGeometry.exists_shrinkingOpens_source`: a neighbourhood of the distinguished point of
  the smooth scheme all of whose standard open subneighbourhoods are realised as the smooth open
  of a shrinking whose source open lies in a prescribed neighbourhood of `x`.
* `AlgebraicGeometry.exists_stageIsStandardRestriction_of_shrinkingOpens`: the same conclusion
  starting from the four opens rather than from a standard shrinking.

## Implementation notes

The square formed by the two closed immersions of a standard restriction is *not* cartesian,
and the square formed by the two smooth structure morphisms is not either: only the square of
the finite morphisms is, and only that one is needed. It is what makes the module on the
restricted closed subscheme the inverse image of the original one, hence the free-module map
the inverse image of the original one, hence the cokernel of the restricted stage the inverse
image of the cokernel. That the restricted free-module map is still invertible over the generic
point of the distinguished fibre uses instead the two *open immersions*: an open immersion into
an irreducible space carries the generic point to the generic point, which identifies the
generic point of the restricted fibre with that of the original one.

A standard shrinking identifies the schemes of the restricted dévissage with the schemes of the
chosen opens only up to heterogeneous equality, and the module on the restricted closed
subscheme with the restriction of the original one in the same way. The open immersions `j_Z`,
`j_Y` of the standard restriction are therefore the identifications composed with the
inclusions of the opens, and the module is compared by
`AlgebraicGeometry.OneStepDevissageAt.ofClosedModuleIso`, which replaces it by the honest
inverse image so that the identification of the modules required by a standard restriction
holds by definition.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-! ### Transport along heterogeneous equalities -/

/-- A morphism heterogeneously equal to `f.resLE U V e` commutes with the inclusions of the opens
`V` and `U`, once its source and target are identified with `V` and `U`. -/
private lemma eqToHom_comp_ι_comp_of_heq {X Y A B : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens}
    {V : X.Opens} (e : V ≤ f ⁻¹ᵁ U) (eA : A = V.toScheme) (eB : B = U.toScheme) {p : A ⟶ B}
    (h : HEq p (f.resLE U V e)) : (eqToHom eA ≫ V.ι) ≫ f = p ≫ eqToHom eB ≫ U.ι := by
  rw [(CategoryTheory.conj_eqToHom_iff_heq p _ eA eB).2 h]
  simp

/-- An identification of two schemes carries a point to any heterogeneously equal point. -/
private lemma eqToHom_apply_of_heq {X Y : Scheme.{u}} (e : X = Y) {x : X} {y : Y}
    (h : HEq x y) : (eqToHom e) x = y := by
  subst e
  cases h
  rfl

/-- An open immersion heterogeneously equal to the inclusion of an open has that open as its
range. -/
lemma opensRange_eq_of_heq_ι {X Y : Scheme.{u}} (U : Y.Opens) (j : X ⟶ Y)
    [IsOpenImmersion j] (hX : X = U.toScheme) (hj : HEq j U.ι) : j.opensRange = U := by
  subst hX
  obtain rfl := eq_of_heq hj
  exact Scheme.Opens.opensRange_ι U

/-- A module heterogeneously equal to the restriction of another one along an open immersion is
its inverse image along that open immersion, read through the identification of the two
schemes. -/
private def pullbackIsoOfHEqRestrict {Z Z' T : Scheme.{u}} (j : T ⟶ Z) [IsOpenImmersion j]
    (G : Z.Modules) (G' : Z'.Modules) (e : Z' = T) (hG : HEq G' (G.restrict j)) :
    G' ≅ (Scheme.Modules.pullback (eqToHom e ≫ j)).obj G := by
  subst e
  cases hG
  exact (Scheme.Modules.restrictFunctorIsoPullback j).app G ≪≫
    (Scheme.Modules.pullbackCongr (Category.id_comp j).symm).app G

/-! ### Generic points of the fibres of a restricted morphism -/

/-- In a commuting square whose horizontal morphisms are open immersions and whose left vertical
morphism has geometrically irreducible fibres, the generic point of a fibre of the right
vertical morphism is carried to the generic point of the corresponding fibre. -/
lemma map_fiberι_genericPoint_of_isOpenImmersion {Y S Y' S' : Scheme.{u}} (g : Y ⟶ S)
    (g' : Y' ⟶ S') (jY : Y' ⟶ Y) (jS : S' ⟶ S) [hjY : IsOpenImmersion jY]
    [IsOpenImmersion jS] [GeometricallyIrreducible g] (comm : jY ≫ g = g' ≫ jS) {s : S}
    {s' : S'} (hs : jS s' = s)
    {η : g.fiber s} {η' : g'.fiber s'} (hη : IsGenericPoint η Set.univ)
    (hη' : IsGenericPoint η' Set.univ) : jY (g'.fiberι s' η') = g.fiberι s η := by
  have hset : g' ⁻¹' {s'} = jY ⁻¹' (g ⁻¹' {s}) := by
    ext y
    change g' y = s' ↔ g (jY y) = s
    rw [← hs, ← Scheme.Hom.comp_apply, comm, Scheme.Hom.comp_apply]
    exact jS.isOpenEmbedding.injective.eq_iff.symm
  let e : g'.fiber s' ≃ₜ (jY ⁻¹' (g ⁻¹' {s})) :=
    (g'.fiberHomeo s').trans (Homeomorph.setCongr hset)
  let j := (g.fiberHomeo s).symm ∘ (g ⁻¹' {s}).restrictPreimage jY ∘ e
  have hj : Topology.IsOpenEmbedding j :=
    (g.fiberHomeo s).symm.isOpenEmbedding.comp
      ((jY.isOpenEmbedding.restrictPreimage (g ⁻¹' {s})).comp e.isOpenEmbedding)
  have hcongr := congrArg (g.fiberι s)
    (IsGenericPoint.map_eq_of_isOpenEmbedding hj hη' hη)
  simpa [j, e, Homeomorph.setCongr, Set.restrictPreimage, Scheme.Hom.fiberHomeo_apply]
    using hcongr

/-! ### The cokernel of a standard restriction -/

section Cokernel

variable {X S X' S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'} {F : X.Modules} {F' : X'.Modules}
  {s : S} {s' : S'} [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType]
  [LocallyOfFiniteType f'] [F'.IsQuasicoherent] [F'.IsFiniteType] {jS : S' ⟶ S} {jX : X' ⟶ X}
  {D : DevissageStage f F s} {D' : DevissageStage f' F' s'}

/-- The cokernel of the free-module map of a standard restriction of a stage is the restriction
of the cokernel of the free-module map of the original stage, provided the square formed by the
two finite morphisms is cartesian. -/
def cokernelIsoOfStageIsStandardRestriction (h : StageIsStandardRestriction jS jX D D')
    (hcart : IsPullback h.jZ D'.oneStep.π D.oneStep.π h.jY) :
    (Scheme.Modules.pullback h.jY).obj D.coker ≅ D'.coker :=
  cokernelIsoOfAlphaComparison hcart h.G_eq h.rank_eq h.alpha_restrict

/-- A stage whose free-module map has zero cokernel restricts to a stage whose free-module map
has zero cokernel. -/
lemma isZero_coker_of_stageIsStandardRestriction (h : StageIsStandardRestriction jS jX D D')
    (hcart : IsPullback h.jZ D'.oneStep.π D.oneStep.π h.jY) (hz : IsZero D.coker) :
    IsZero D'.coker :=
  ((Scheme.Modules.pullback h.jY).map_isZero hz).of_iso
    (cokernelIsoOfStageIsStandardRestriction h hcart).symm

end Cokernel

/-! ### A stage restriction out of a standard shrinking -/

/-- A standard shrinking of the one-step dévissage at the distinguished point of a stage, whose
square of finite morphisms is cartesian, exhibits the restricted system as a stage of a complete
dévissage which is a standard restriction of the given one, pointed at the same point. The
module of the restricted stage may be replaced by any isomorphic one; this is what carries the
comparison of the cokernels into the next stage of a chain. -/
lemma exists_stageIsStandardRestriction_of_standardShrinking {X S : Scheme.{u}} {f : X ⟶ S}
    {F : X.Modules} {x : X} [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType]
    (D : DevissageStage f F (f x)) (P : PointedDevissageStage f F (f x) x D)
    (E : OneStepDevissageAt.StandardShrinking f F x P.atPoint)
    (hπ : E.Z' = P.atPoint.toOneStepDevissage.π ⁻¹ᵁ E.Y') (M : E.X'.toScheme.Modules)
    [hqM : M.IsQuasicoherent] [htM : M.IsFiniteType] (eM : M ≅ F.restrict E.X'.ι)
    {s' : E.S'.toScheme} (hs' : E.restricted_morphism ⟨x, E.mem_source⟩ = s') :
    letI := E.locally_finite_type
    ∃ D' : DevissageStage E.restricted_morphism M s',
      ∃ P' : PointedDevissageStage E.restricted_morphism M s' ⟨x, E.mem_source⟩ D',
        ∃ R : StageIsStandardRestriction E.S'.ι E.X'.ι D D',
          ∃ _ : PointedStageIsStandardRestriction E.S'.ι E.X'.ι P P' R,
            IsPullback R.jZ D'.oneStep.π D.oneStep.π R.jY ∧ D'.oneStep.Y = E.Y'.toScheme ∧
              HEq R.jY E.Y'.ι ∧
              HEq D'.oneStep.g (P.atPoint.toOneStepDevissage.g.resLE E.S' E.Y'
                E.smooth_over_base) ∧
              HEq P'.y (⟨P.atPoint.y, E.mem_smooth⟩ : E.Y'.toScheme) := by
  subst hs'
  cases D with
  | mk step rank alpha η hη hα =>
    cases P with
    | mk A hA y hy =>
      cases hA
      cases hy
      have := E.locally_finite_type
      have := E.quasi_coherent
      have := E.finite_type
      let A₀ := E.restricted_devissage
      have eZ : A₀.toOneStepDevissage.Z = E.Z'.toScheme := eq_of_heq E.restricted_closed
      have eY : A₀.toOneStepDevissage.Y = E.Y'.toScheme := eq_of_heq E.restricted_smooth
      let jZ : A₀.toOneStepDevissage.Z ⟶ A.toOneStepDevissage.Z := eqToHom eZ ≫ E.Z'.ι
      let jY : A₀.toOneStepDevissage.Y ⟶ A.toOneStepDevissage.Y := eqToHom eY ≫ E.Y'.ι
      have hoZ : IsOpenImmersion jZ :=
        inferInstanceAs (IsOpenImmersion (eqToHom eZ ≫ E.Z'.ι))
      have hoY : IsOpenImmersion jY :=
        inferInstanceAs (IsOpenImmersion (eqToHom eY ≫ E.Y'.ι))
      have hjZ : jZ.opensRange = E.Z' :=
        (Scheme.Hom.opensRange_comp_of_isIso (eqToHom eZ) E.Z'.ι).trans E.Z'.opensRange_ι
      have hjY : jY.opensRange = E.Y' :=
        (Scheme.Hom.opensRange_comp_of_isIso (eqToHom eY) E.Y'.ι).trans E.Y'.opensRange_ι
      have hiComm : jZ ≫ A.toOneStepDevissage.i = A₀.toOneStepDevissage.i ≫ E.X'.ι := by
        simpa [jZ] using eqToHom_comp_ι_comp_of_heq _ E.closed_over_source eZ rfl
          E.restricted_closed_map
      have hπComm : jZ ≫ A.toOneStepDevissage.π = A₀.toOneStepDevissage.π ≫ jY :=
        eqToHom_comp_ι_comp_of_heq _ E.closed_over_smooth eZ eY E.restricted_finite_map
      have hgComm : jY ≫ A.toOneStepDevissage.g = A₀.toOneStepDevissage.g ≫ E.S'.ι := by
        simpa [jY] using eqToHom_comp_ι_comp_of_heq _ E.smooth_over_base eY rfl
          E.restricted_smooth_map
      have hcart : IsPullback jZ A₀.toOneStepDevissage.π A.toOneStepDevissage.π jY :=
        (IsOpenImmersion.isPullback A₀.toOneStepDevissage.π jZ jY A.toOneStepDevissage.π
          hπComm (by rw [hjY, hjZ, hπ])).flip
      have := A.toOneStepDevissage.quasi_coherent_G
      have := A.toOneStepDevissage.finite_type_G
      have hGft : ((Scheme.Modules.pullback jZ).obj A.toOneStepDevissage.G).IsFiniteType :=
        SheafOfModules.pullback_isFiniteType jZ.toLRSHom.toShHom A.toOneStepDevissage.G
      have eG : A₀.toOneStepDevissage.G ≅ (Scheme.Modules.pullback jZ).obj
          A.toOneStepDevissage.G :=
        pullbackIsoOfHEqRestrict E.Z'.ι A.toOneStepDevissage.G A₀.toOneStepDevissage.G eZ
          E.restricted_closed_module
      have hGqc : ((Scheme.Modules.pullback jZ).obj A.toOneStepDevissage.G).IsQuasicoherent :=
        SheafOfModules.isQuasicoherent_of_iso eG A₀.toOneStepDevissage.quasi_coherent_G
      let A' := (A₀.ofClosedModuleIso _ hGqc hGft eG.symm).ofModuleIso eM
      have : GeometricallyIrreducible A.toOneStepDevissage.g :=
        A.toOneStepDevissage.geometrically_irreducible
      let s' := E.restricted_morphism ⟨x, E.mem_source⟩
      have hs : E.S'.ι s' = f x := by
        change E.S'.ι (E.restricted_morphism ⟨x, E.mem_source⟩) = f x
        rw [E.restricted_morphism_eq]
        exact Scheme.Hom.coe_resLE_apply _ _ _
      have hcartA : IsPullback jZ A'.toOneStepDevissage.π A.toOneStepDevissage.π jY := hcart
      have hGA : A'.toOneStepDevissage.G = (Scheme.Modules.pullback jZ).obj
        A.toOneStepDevissage.G := rfl
      have hηmap : jY (A'.toOneStepDevissage.g.fiberι s'
          A'.toOneStepDevissage.fiberGenericPoint) = A.toOneStepDevissage.g.fiberι (f x) η :=
        map_fiberι_genericPoint_of_isOpenImmersion A.toOneStepDevissage.g
          A'.toOneStepDevissage.g jY E.S'.ι (hjY := hoY) hgComm hs hη
          A'.toOneStepDevissage.isGenericPoint_fiberGenericPoint
      let D' : DevissageStage E.restricted_morphism M s' :=
        { oneStep := A'.toOneStepDevissage
          rank := rank
          alpha := baseChangedAlpha ⟨A.toOneStepDevissage, rank, alpha, η, hη, hα⟩
            A'.toOneStepDevissage hcartA hGA
          genericPoint := A'.toOneStepDevissage.fiberGenericPoint
          genericPoint_spec := A'.toOneStepDevissage.isGenericPoint_fiberGenericPoint
          genericFiber_isIso := isIso_baseChangedAlpha_of_map_eq
            ⟨A.toOneStepDevissage, rank, alpha, η, hη, hα⟩ A'.toOneStepDevissage hcartA hGA
            hηmap }
      let R : StageIsStandardRestriction E.S'.ι E.X'.ι
          ⟨A.toOneStepDevissage, rank, alpha, η, hη, hα⟩ D' :=
        { jZ := jZ
          jY := jY
          openImmersion_jZ := hoZ
          openImmersion_jY := hoY
          closed_section := E.closed_section
          smooth_section := E.smooth_section
          closed_standard := hjZ.trans E.closed_standard
          smooth_standard := hjY.trans E.smooth_standard
          closed_comm := hiComm
          finite_comm := hπComm
          smooth_comm := hgComm
          G_eq := hGA
          rank_eq := rfl
          alpha_restrict := baseChangedAlpha_comp
            ⟨A.toOneStepDevissage, rank, alpha, η, hη, hα⟩ A'.toOneStepDevissage hcartA hGA }
      have hzpt : jZ A'.z = A.z := congrArg E.Z'.ι (eqToHom_apply_of_heq eZ E.restricted_z)
      have hypt : jY A'.y = A.y := congrArg E.Y'.ι (eqToHom_apply_of_heq eY E.restricted_y)
      refine ⟨D', ⟨A', HEq.rfl, A'.y, HEq.rfl⟩, R, ?_, hcart, eY, ?_, E.restricted_smooth_map,
        E.restricted_y⟩
      · exact
          { x_eq := rfl
            y_eq := hypt
            z := A.z
            z' := A'.z
            z_eq := hzpt
            z_is_pointed := HEq.rfl
            z'_is_pointed := HEq.rfl }
      · change HEq (eqToHom eY ≫ E.Y'.ι) E.Y'.ι
        exact eqToHom_comp_heq E.Y'.ι eY

/-! ### The four opens of a shrinking -/

/-- A choice of four principal opens shrinking a one-step dévissage of `F/X/S` over `s`, at a
point `x` of the source and a point `y` of the smooth scheme: principal opens `S'` of the base
and `X'` of the source containing `f x` and `x`, and principal opens `Z'` of the closed
subscheme and `Y'` of the smooth scheme with `y ∈ Y'`, where `Z'` is cut out both by `X'` and
by `Y'` and where `Y'` still covers `S'`.

This records exactly the data that `AlgebraicGeometry.standardShrinkingOfOpens` turns into a
standard shrinking, strengthened in the two ways an induction over a whole chain of stages
needs: the two inclusions of `Z'` are equalities, so that the square of the finite morphisms of
the shrinking is cartesian, and the restricted smooth morphism is surjective, which a standard
shrinking does not record. Both are stable under shrinking the base further. -/
structure OneStepDevissage.ShrinkingOpens {X S : Scheme.{u}} {f : X ⟶ S} {F : X.Modules}
    {s : S} [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType]
    (D : OneStepDevissage f F s) (x : X) (y : D.Y) (S' : S.Opens) (X' : X.Opens) where
  /-- The principal open of the closed subscheme. -/
  Z' : D.Z.Opens
  /-- The principal open of the smooth scheme. -/
  Y' : D.Y.Opens
  /-- A global function cutting out `S'`. -/
  base_section : Γ(S, ⊤)
  /-- A global function cutting out `X'`. -/
  source_section : Γ(X, ⊤)
  /-- A global function cutting out `Z'`. -/
  closed_section : Γ(D.Z, ⊤)
  /-- A global function cutting out `Y'`. -/
  smooth_section : Γ(D.Y, ⊤)
  base_standard : S' = S.basicOpen base_section
  source_standard : X' = X.basicOpen source_section
  closed_standard : Z' = D.Z.basicOpen closed_section
  smooth_standard : Y' = D.Y.basicOpen smooth_section
  mem_base : f x ∈ S'
  mem_source : x ∈ X'
  mem_smooth : y ∈ Y'
  source_over_base : X' ≤ f ⁻¹ᵁ S'
  closed_eq_source : Z' = D.i ⁻¹ᵁ X'
  closed_eq_smooth : Z' = D.π ⁻¹ᵁ Y'
  smooth_over_base : Y' ≤ D.g ⁻¹ᵁ S'
  smooth_surjOn : ∀ t : S, t ∈ S' → ∃ p : D.Y, p ∈ Y' ∧ D.g p = t

namespace OneStepDevissage.ShrinkingOpens

variable {X S : Scheme.{u}} {f : X ⟶ S} {F : X.Modules} {s : S} [LocallyOfFiniteType f]
  [F.IsQuasicoherent] [F.IsFiniteType] {D : OneStepDevissage f F s} {x : X} {y : D.Y}
  {S' : S.Opens} {X' : X.Opens}

/-- Shrinking the base of a choice of four opens to a smaller principal open: all four opens are
cut down by the inverse image of the new base. -/
def restrict (A : D.ShrinkingOpens x y S' X') (S'' : S.Opens) (a : Γ(S, ⊤))
    (hS'' : S'' = S.basicOpen a) (hsub : S'' ≤ S') (hs'' : f x ∈ S'') (hgy : D.g y = f x) :
    D.ShrinkingOpens x y S'' (X' ⊓ f ⁻¹ᵁ S'') where
  Z' := A.Z' ⊓ (D.i ≫ f) ⁻¹ᵁ S''
  Y' := A.Y' ⊓ D.g ⁻¹ᵁ S''
  base_section := a
  source_section := A.source_section * f.appTop a
  closed_section := A.closed_section * (D.i ≫ f).appTop a
  smooth_section := A.smooth_section * D.g.appTop a
  base_standard := hS''
  source_standard := by
    rw [Scheme.basicOpen_mul, ← Scheme.preimage_basicOpen_top, ← A.source_standard, ← hS'']
  closed_standard := by
    rw [Scheme.basicOpen_mul, ← Scheme.preimage_basicOpen_top, ← A.closed_standard, ← hS'']
  smooth_standard := by
    rw [Scheme.basicOpen_mul, ← Scheme.preimage_basicOpen_top, ← A.smooth_standard, ← hS'']
  mem_base := hs''
  mem_source := ⟨A.mem_source, hs''⟩
  mem_smooth := ⟨A.mem_smooth, by change D.g y ∈ S''; rwa [hgy]⟩
  source_over_base := inf_le_right
  closed_eq_source := by
    rw [Scheme.Hom.preimage_inf, A.closed_eq_source, Scheme.Hom.comp_preimage]
  closed_eq_smooth := by
    rw [Scheme.Hom.preimage_inf, A.closed_eq_smooth, D.over_base, Scheme.Hom.comp_preimage]
  smooth_over_base := inf_le_right
  smooth_surjOn t ht := by
    obtain ⟨p, hp, hpt⟩ := A.smooth_surjOn t (hsub ht)
    exact ⟨p, ⟨hp, by change D.g p ∈ S''; rwa [hpt]⟩, hpt⟩

end OneStepDevissage.ShrinkingOpens

/-- The common refinement of Stacks 05HA (2) and (3) for a choice of four opens: a prescribed
principal open neighbourhood `W` of the distinguished point of the smooth scheme of a one-step
dévissage at `x` occurs, cut down to a principal open of the base, as the smooth open, and at
the same time the source open lies inside a prescribed principal open neighbourhood `U₀` of
`x`, provided that the inverse image of `W` in the closed subscheme already lies over `U₀`.

The base is chosen inside the image of `W`, which is open because the smooth morphism is open,
so that the restricted smooth morphism is surjective, and the open of the closed subscheme is
the full inverse image of `W` cut down to the base. Enlarging the source open by `U₀` does not
change that inverse image, exactly because of the hypothesis `hWU`. -/
lemma exists_shrinkingOpens_smooth_inside {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (x : X)
    [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType] (D : OneStepDevissageAt f F x)
    (W : D.toOneStepDevissage.Y.Opens) (a : Γ(D.toOneStepDevissage.Y, ⊤))
    (hW : W = D.toOneStepDevissage.Y.basicOpen a) (hy : D.y ∈ W) (U₀ : X.Opens) (b : Γ(X, ⊤))
    (hU₀ : U₀ = X.basicOpen b) (hx : x ∈ U₀)
    (hWU : D.toOneStepDevissage.π ⁻¹ᵁ W ≤ D.toOneStepDevissage.i ⁻¹ᵁ U₀) :
    ∃ (S' : S.Opens) (X' : X.Opens) (A : D.toOneStepDevissage.ShrinkingOpens x D.y S' X'),
      A.Y' = W ⊓ (D.toOneStepDevissage.g ⁻¹ᵁ S') ∧ X' ≤ U₀ := by
  let A := D.toOneStepDevissage
  have : IsAffine X := A.affine_X
  have : IsAffine S := A.affine_S
  have : IsClosedImmersion A.i := A.closed_immersion
  have : Smooth A.g := A.smooth
  let O : S.Opens := ⟨A.g '' (W : Set A.Y), A.g.isOpenMap _ W.isOpen⟩
  have hsO : f x ∈ O := ⟨D.y, hy, D.g_y⟩
  obtain ⟨c, hcO, hc⟩ := (isAffineOpen_top S).exists_basicOpen_le (⟨f x, hsO⟩ : O) trivial
  obtain ⟨h, hh⟩ := A.i.app_surjective ⊤ (isAffineOpen_top X) (A.π.appTop a)
  have hpre : A.i ⁻¹ᵁ X.basicOpen h = A.π ⁻¹ᵁ W := by
    rw [hW, Scheme.preimage_basicOpen_top, Scheme.preimage_basicOpen_top]
    exact congrArg A.Z.basicOpen hh
  have hd : W ⊓ A.g ⁻¹ᵁ S.basicOpen c = A.Y.basicOpen (a * A.g.appTop c) := by
    rw [hW, Scheme.basicOpen_mul, ← Scheme.preimage_basicOpen_top]
  have hzW : A.π D.z ∈ W := by rwa [D.π_z]
  refine ⟨S.basicOpen c, X.basicOpen h ⊓ U₀ ⊓ f ⁻¹ᵁ S.basicOpen c,
    { Z' := A.π ⁻¹ᵁ (W ⊓ A.g ⁻¹ᵁ S.basicOpen c)
      Y' := W ⊓ A.g ⁻¹ᵁ S.basicOpen c
      base_section := c
      source_section := h * b * f.appTop c
      closed_section := A.π.appTop (a * A.g.appTop c)
      smooth_section := a * A.g.appTop c
      base_standard := rfl
      source_standard := by
        rw [Scheme.basicOpen_mul, Scheme.basicOpen_mul, ← Scheme.preimage_basicOpen_top, hU₀]
      closed_standard := by rw [hd, Scheme.preimage_basicOpen_top]
      smooth_standard := hd
      mem_base := hc
      mem_source := ⟨⟨by rw [← D.i_z]; exact hpre.ge hzW, hx⟩, hc⟩
      mem_smooth := ⟨hy, by change A.g D.y ∈ S.basicOpen c; rwa [D.g_y]⟩
      source_over_base := inf_le_right
      closed_eq_source := by
        rw [Scheme.Hom.preimage_inf, Scheme.Hom.preimage_inf, Scheme.Hom.preimage_inf, hpre,
          ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, A.over_base,
          inf_eq_left.mpr hWU]
      closed_eq_smooth := rfl
      smooth_over_base := inf_le_right
      smooth_surjOn := fun t ht => by
        obtain ⟨p, hpW, hpt⟩ := hcO ht
        exact ⟨p, ⟨hpW, by change A.g p ∈ S.basicOpen c; rwa [hpt]⟩, hpt⟩ },
    rfl, inf_le_left.trans inf_le_right⟩

/-- A prescribed principal open neighbourhood `W` of the distinguished point of the smooth scheme
of a one-step dévissage at `x` occurs, cut down to a principal open of the base, as the smooth
open of a choice of four opens. This is the cartesian refinement of Stacks 05HA (2). -/
lemma exists_shrinkingOpens_smooth {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (x : X)
    [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType] (D : OneStepDevissageAt f F x)
    (W : D.toOneStepDevissage.Y.Opens) (a : Γ(D.toOneStepDevissage.Y, ⊤))
    (hW : W = D.toOneStepDevissage.Y.basicOpen a) (hy : D.y ∈ W) :
    ∃ (S' : S.Opens) (X' : X.Opens) (A : D.toOneStepDevissage.ShrinkingOpens x D.y S' X'),
      A.Y' = W ⊓ (D.toOneStepDevissage.g ⁻¹ᵁ S') := by
  obtain ⟨S', X', A, hA, -⟩ :=
    exists_shrinkingOpens_smooth_inside f F x D W a hW hy ⊤ 1 (by simp) trivial (by simp)
  exact ⟨S', X', A, hA⟩

/-- Given an open neighbourhood `U` of `x`, there is a principal open neighbourhood `V` of the
distinguished point of the smooth scheme of a one-step dévissage at `x` such that *every*
principal open neighbourhood of that point inside `V` is the smooth open of a choice of four
opens whose source open lies inside `U`.

This is the cartesian refinement of Stacks 05HA (3), in the form an induction over a chain of
stages needs: the smooth open is not determined by `U`, because the stage above has already
fixed its source open, and the only thing the induction can insist on is that the choice is
small enough. Smallness is uniform in the choice: `V` is a neighbourhood whose inverse image in
the closed subscheme lies over a principal neighbourhood of `x` inside `U`, which exists because
the finite morphism of the dévissage has `x` as the only point of the fibre over the
distinguished point. -/
lemma exists_shrinkingOpens_source {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (x : X)
    [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType] (D : OneStepDevissageAt f F x)
    (U : X.Opens) (hx : x ∈ U) :
    ∃ (V : D.toOneStepDevissage.Y.Opens) (d : Γ(D.toOneStepDevissage.Y, ⊤)),
      V = D.toOneStepDevissage.Y.basicOpen d ∧ D.y ∈ V ∧
        ∀ (W : D.toOneStepDevissage.Y.Opens) (c : Γ(D.toOneStepDevissage.Y, ⊤)),
          W = D.toOneStepDevissage.Y.basicOpen c → D.y ∈ W → W ≤ V →
            ∃ (S' : S.Opens) (X' : X.Opens)
              (A : D.toOneStepDevissage.ShrinkingOpens x D.y S' X'),
              A.Y' = W ⊓ (D.toOneStepDevissage.g ⁻¹ᵁ S') ∧ X' ≤ U := by
  let A := D.toOneStepDevissage
  have : IsAffine X := A.affine_X
  have : IsAffine A.Y := A.affine_Y
  have : IsFinite A.π := A.finite
  obtain ⟨b, hbU, hb⟩ := (isAffineOpen_top X).exists_basicOpen_le (⟨x, hx⟩ : U) trivial
  have hz : D.z ∈ A.i ⁻¹ᵁ X.basicOpen b := by
    change A.i D.z ∈ X.basicOpen b
    rwa [D.i_z]
  obtain ⟨V₀, hy, hV₀⟩ :=
    exists_open_preimage_le A.π D.z D.y D.π_z D.fiber_eq_singleton (A.i ⁻¹ᵁ X.basicOpen b) hz
  obtain ⟨d, hdV, hd⟩ := (isAffineOpen_top A.Y).exists_basicOpen_le (⟨D.y, hy⟩ : V₀) trivial
  refine ⟨A.Y.basicOpen d, d, rfl, hd, fun W c hWc hyW hWV => ?_⟩
  obtain ⟨S', X', B, hB, hXU⟩ := exists_shrinkingOpens_smooth_inside f F x D W c hWc hyW
    (X.basicOpen b) b rfl hb ((A.π.preimage_mono (hWV.trans hdV)).trans hV₀)
  exact ⟨S', X', B, hB, hXU.trans hbU⟩

/-- The four opens of a shrinking realise a stage of a complete dévissage as a standard
restriction of the given one, pointed at the same point: the restricted system is assembled by
`AlgebraicGeometry.standardShrinkingOfOpens`, and the square of the finite morphisms is
cartesian because the open of the closed subscheme is the full inverse image of the open of the
smooth scheme. -/
lemma exists_stageIsStandardRestriction_of_shrinkingOpens {X S : Scheme.{u}} {f : X ⟶ S}
    {F : X.Modules} {x : X} [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType]
    (D : DevissageStage f F (f x)) (P : PointedDevissageStage f F (f x) x D) {S' : S.Opens}
    {X' : X.Opens} (A : D.oneStep.ShrinkingOpens x P.y S' X') (M : X'.toScheme.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] (eM : M ≅ F.restrict X'.ι) :
    letI := locallyOfFiniteType_resLE f S' X' A.source_over_base
    ∃ D' : DevissageStage (f.resLE S' X' A.source_over_base) M ⟨f x, A.mem_base⟩,
      ∃ P' : PointedDevissageStage (f.resLE S' X' A.source_over_base) M ⟨f x, A.mem_base⟩
          ⟨x, A.mem_source⟩ D',
        ∃ R : StageIsStandardRestriction S'.ι X'.ι D D',
          ∃ _ : PointedStageIsStandardRestriction S'.ι X'.ι P P' R,
            IsPullback R.jZ D'.oneStep.π D.oneStep.π R.jY ∧ D'.oneStep.Y = A.Y'.toScheme ∧
              HEq R.jY A.Y'.ι ∧
              HEq D'.oneStep.g (D.oneStep.g.resLE S' A.Y' A.smooth_over_base) ∧
              HEq P'.y (⟨P.y, A.mem_smooth⟩ : A.Y'.toScheme) := by
  cases D with
  | mk step rank alpha η hη hα =>
    cases P with
    | mk B hB y hy =>
      cases hB
      cases hy
      have hsurj : Surjective (B.toOneStepDevissage.g.resLE S' A.Y' A.smooth_over_base) := ⟨by
        intro t
        obtain ⟨p, hp, hpt⟩ := A.smooth_surjOn t.val t.property
        exact ⟨⟨p, hp⟩, (resLE_apply_eq_iff B.toOneStepDevissage.g A.smooth_over_base _ t).2 hpt⟩⟩
      have hmemZ : B.z ∈ A.Z' := by
        rw [A.closed_eq_source]
        change B.toOneStepDevissage.i B.z ∈ X'
        rw [B.i_z]
        exact A.mem_source
      have H := exists_stageIsStandardRestriction_of_standardShrinking
        ⟨B.toOneStepDevissage, rank, alpha, η, hη, hα⟩ ⟨B, HEq.rfl, B.y, HEq.rfl⟩
        (standardShrinkingOfOpens f F x B S' X' A.Z' A.Y' A.base_section A.source_section
          A.closed_section A.smooth_section A.base_standard A.source_standard A.closed_standard
          A.smooth_standard A.mem_base A.mem_source hmemZ A.mem_smooth A.source_over_base
          A.closed_eq_source A.closed_eq_smooth A.smooth_over_base)
        A.closed_eq_smooth M (hqM := ‹M.IsQuasicoherent›) (htM := ‹M.IsFiniteType›) eM
        (s' := (⟨f x, A.mem_base⟩ : S'.toScheme))
        (Subtype.ext (Scheme.Hom.coe_resLE_apply f A.source_over_base ⟨x, A.mem_source⟩))
      exact H

end AlgebraicGeometry

end
