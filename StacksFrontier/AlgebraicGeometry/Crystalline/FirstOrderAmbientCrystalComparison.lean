module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedPoint
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.AmbientSchemeComparison
public import StacksFrontier.AlgebraicGeometry.Crystalline.FirstOrderIdealKernelIso

/-!
# The comparison map of a crystal, read on the ambient schemes

Let `F` be a sheaf of `𝒪_{X/S}`-modules on the big crystalline site `CRIS(X/S)` of a global
crystalline situation and let `g : (U, T, δ) ⟶ (U', T', δ')` be a morphism of that site.  The
comparison map of [Stacks, Tag 07IQ] has two spellings, over two different sheaves of rings on
the ambient scheme `T`:

* `Crystalline.GlobalCrystallineSituation.Thickening.moduleComparisonSheaf`, written over the
  restrictions of `𝒪_{X/S}` to the opens of the ambient schemes, which is the map the crystal
  condition `Crystalline.GlobalCrystallineSituation.IsSheafCrystal` of [Stacks, Tag 07IS]
  declares invertible; and
* `Crystalline.GlobalCrystallineSituation.ambientSchemeCrystalComparison`, written over the
  structure sheaves of the ambient schemes.

This module shows that invertibility of the first spelling implies invertibility of the second.

## The transport

Both maps are transposes of one and the same `f`-map `F_{T'} ⟶ g_* F_T`, along two adjunctions
with the *same* right adjoint — the two adjunctions out of which
`Crystalline.GlobalCrystallineSituation.Thickening.ambientSchemePullbackIso` is built by
uniqueness of left adjoints.  Transposes of a fixed morphism along two adjunctions sharing a
right adjoint differ by precomposition with the comparison isomorphism of the two left adjoints,
so one is invertible exactly when the other is; that is
`Stacks.Adjunction.homEquiv_symm_eq_leftAdjointUniq`.  The two spellings of the `f`-map are
related by `Crystalline.GlobalCrystallineSituation.Thickening.ambientSchemePushforwardIso`; this
relation is the definition of `Crystalline.GlobalCrystallineSituation.Thickening.ambientFMap`.

What is left is the change of scalars between a module read over the restriction of `𝒪_{X/S}` to
the ambient scheme and the same module read over the structure sheaf of that scheme.  It is
absorbed by the counits of `Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso`, isomorphisms
because restriction of scalars along an isomorphism of sheaves of rings is an equivalence by
`Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso`.  The abstract form of this
transport is `Stacks.Adjunction.isIso_homEquiv_symm_comp_natIso`.

## Main results

* `Stacks.Adjunction.homEquiv_symm_eq_leftAdjointUniq` and
  `Stacks.Adjunction.isIso_homEquiv_symm_of` — the transposes of a morphism along two adjunctions
  with the same right adjoint differ by precomposition with an isomorphism, hence are invertible
  together.
* `Stacks.Adjunction.isIso_homEquiv_symm_comp_natIso` — the transport in the abstract, for a pair
  of adjunctions conjugated by two restriction-of-scalars adjunctions and a natural isomorphism
  of their right adjoints.
* `Crystalline.GlobalCrystallineSituation.Thickening.isIso_homEquiv_symm_ambientFMap` — for a
  crystal in `𝒪_{X/S}`-modules the comparison map of [Stacks, Tag 07IQ] at any morphism of
  `CRIS(X/S)`, read between sheaves of modules on the ambient schemes, is an isomorphism.
* `Crystalline.GlobalCrystallineSituation.isIso_ambientSchemeCrystalComparison` — the same
  statement at the projection `p₀ : T' ⟶ T` of the first-order universal thickening of
  [Stacks, Tag 07J2].

## References

* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
* [Stacks Project, Tag 07IS](https://stacks.math.columbia.edu/tag/07IS)
* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u

noncomputable section

namespace Stacks.Adjunction

/-- **The transposes of a morphism along two adjunctions with the same right adjoint differ by
the comparison isomorphism of the two left adjoints.** -/
theorem homEquiv_symm_eq_leftAdjointUniq {C D : Type*} [Category C] [Category D]
    {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G) {X : C} {Y : D} (φ : X ⟶ G.obj Y) :
    (adj1.homEquiv X Y).symm φ =
      (CategoryTheory.Adjunction.leftAdjointUniq adj1 adj2).hom.app X ≫
        (adj2.homEquiv X Y).symm φ := by
  rw [Equiv.symm_apply_eq, CategoryTheory.Adjunction.homEquiv_unit, Functor.map_comp,
    ← Category.assoc, CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app,
    ← CategoryTheory.Adjunction.homEquiv_unit, Equiv.apply_symm_apply]

/-- **Invertibility of a transpose does not depend on which of two adjunctions with the same
right adjoint it is taken along**, the two transposes differing by precomposition with an
isomorphism. -/
theorem isIso_homEquiv_symm_of {C D : Type*} [Category C] [Category D]
    {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G) {X : C} {Y : D} (φ : X ⟶ G.obj Y)
    (h : IsIso ((adj1.homEquiv X Y).symm φ)) :
    IsIso ((adj2.homEquiv X Y).symm φ) := by
  rw [homEquiv_symm_eq_leftAdjointUniq adj1 adj2 φ] at h
  exact IsIso.of_isIso_comp_left
    ((CategoryTheory.Adjunction.leftAdjointUniq adj1 adj2).hom.app X) _

/-- **The transpose of a morphism along `adjP` is an isomorphism as soon as the transpose of its
other spelling along `adjS` is**, when the two adjunctions are conjugated by `adjB` and `adjA`
and a natural isomorphism `e : I ⋙ G ≅ G' ⋙ L` of the resulting right adjoints, provided `G`,
`G'` and `F'` are equivalences. -/
theorem isIso_homEquiv_symm_comp_natIso {C₁ C₂ C₃ C₄ : Type*} [Category C₁] [Category C₂]
    [Category C₃] [Category C₄] {F : C₁ ⥤ C₂} {G : C₂ ⥤ C₁} (adjB : F ⊣ G)
    {H : C₂ ⥤ C₃} {I : C₃ ⥤ C₂} (adjS : H ⊣ I) {K : C₁ ⥤ C₄} {L : C₄ ⥤ C₁} (adjP : K ⊣ L)
    {F' : C₄ ⥤ C₃} {G' : C₃ ⥤ C₄} (adjA : F' ⊣ G') (e : I ⋙ G ≅ G' ⋙ L)
    {W : C₂} {Y : C₃} (k : W ⟶ I.obj Y) (hG : G.IsEquivalence) (hG' : G'.IsEquivalence)
    (hF' : F'.IsEquivalence) (hk : IsIso ((adjS.homEquiv W Y).symm k)) :
    IsIso ((adjP.homEquiv (G.obj W) (G'.obj Y)).symm (G.map k ≫ e.hom.app Y)) := by
  have h1 : IsIso (((adjB.comp adjS).homEquiv (G.obj W) Y).symm (G.map k)) := by
    have hinner : (adjB.homEquiv (G.obj W) (I.obj Y)).symm (G.map k) =
        adjB.counit.app W ≫ k := by
      rw [CategoryTheory.Adjunction.homEquiv_counit]
      exact adjB.counit.naturality k
    have e1 : ((adjB.comp adjS).homEquiv (G.obj W) Y).symm (G.map k) =
        H.map (adjB.counit.app W) ≫ (adjS.homEquiv W Y).symm k := by
      rw [CategoryTheory.Adjunction.comp_homEquiv, Equiv.symm_trans_apply, hinner,
        CategoryTheory.Adjunction.homEquiv_naturality_left_symm]
      rfl
    rw [e1]
    infer_instance
  have h2 := isIso_homEquiv_symm_of (adjB.comp adjS)
    ((adjP.comp adjA).ofNatIsoRight e.symm) (G.map k) h1
  have e3 : (((adjP.comp adjA).ofNatIsoRight e.symm).homEquiv (G.obj W) Y).symm (G.map k) =
      F'.map ((adjP.homEquiv (G.obj W) (G'.obj Y)).symm (G.map k ≫ e.hom.app Y)) ≫
        adjA.counit.app Y := by
    rw [CategoryTheory.Adjunction.homEquiv_ofNatIsoRight_symm_apply,
      CategoryTheory.Adjunction.comp_homEquiv, Equiv.symm_trans_apply,
      CategoryTheory.Adjunction.homEquiv_counit]
    rfl
  rw [e3] at h2
  have := IsIso.of_isIso_comp_right
    (F'.map ((adjP.homEquiv (G.obj W) (G'.obj Y)).symm (G.map k ≫ e.hom.app Y)))
    (adjA.counit.app Y)
  exact isIso_of_reflects_iso _ F'

end Stacks.Adjunction

namespace Crystalline.GlobalCrystallineSituation

namespace Thickening

variable {S : GlobalCrystallineSituation.{u}} {A B : Thickening S}
  {M : SheafOfModules.{u} (crystallineStructureSheaf S)}

/-- **Stacks Project, Tag 07IQ.**  For a crystal in `𝒪_{X/S}`-modules the comparison map
`c_g : g^* F_{T'} ⟶ F_T` of a morphism `g : (U, T, δ) ⟶ (U', T', δ')` of `CRIS(X/S)`, read
between sheaves of modules on the *ambient schemes*, is an isomorphism. -/
theorem isIso_homEquiv_symm_ambientFMap (hM : IsSheafCrystal M) (g : A ⟶ B) :
    IsIso (((Scheme.Modules.pullbackPushforwardAdjunction g.targetHom.hom).homEquiv
        (ambientSchemeModule M B) (ambientSchemeModule M A)).symm (ambientFMap M g)) :=
  Stacks.Adjunction.isIso_homEquiv_symm_comp_natIso
    (Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso
      (ringRestrictionSheafStructureIso B))
    (SheafOfModules.pullbackPushforwardAdjunction.{u} (ringRestrictionSheafFMap g))
    (Scheme.Modules.pullbackPushforwardAdjunction g.targetHom.hom)
    (Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso
      (ringRestrictionSheafStructureIso A))
    (ambientSchemePushforwardIso g) (moduleFMapSheaf M g)
    (Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso
      (ringRestrictionSheafStructureIso B)).isEquivalence_functor
    (Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso
      (ringRestrictionSheafStructureIso A)).isEquivalence_functor
    (Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso
      (ringRestrictionSheafStructureIso A)).isEquivalence_inverse
    (hM A B g)

end Thickening

variable {S : GlobalCrystallineSituation.{u}}
  {M : SheafOfModules.{u} (crystallineStructureSheaf S)}

/-- **Stacks Project, Tag 07IQ.**  The comparison map
`Crystalline.GlobalCrystallineSituation.ambientSchemeCrystalComparison` of a crystal in
`𝒪_{X/S}`-modules at the projection `p₀ : T' ⟶ T` of the first-order universal thickening of
[Stacks, Tag 07J2], read between sheaves of modules on the ambient schemes, is an isomorphism. -/
theorem isIso_ambientSchemeCrystalComparison (hM : IsSheafCrystal M) (A : Thickening S) :
    IsIso (ambientSchemeCrystalComparison M A) :=
  Thickening.isIso_homEquiv_symm_ambientFMap hM (firstOrderThickeningSiteP₀ S A)

end Crystalline.GlobalCrystallineSituation

end

end
