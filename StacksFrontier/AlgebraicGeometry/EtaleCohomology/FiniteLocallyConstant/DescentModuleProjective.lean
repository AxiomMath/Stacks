module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.MonodromyDescentIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ConstructibleFlat
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantModules.Morphisms
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.InverseImageSectionsLimit
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.UnibranchLocallyIrreducible

/-!
# The descent module of a locally constant sheaf with finite projective values

Let `G : V ⟶ X` be a Galois covering of an irreducible geometrically unibranch scheme and `F` a
sheaf of `Λ`-modules which is locally constant with finite projective values. If `F` is the
descent sheaf `D(N)` of a module `N` along `G`, then `N` is finite projective: on a nonempty
member `W` of a covering of `V` on which `F` is constant with a finite projective value `E`, both
`E` and `N` are the sections of `F` over an irreducible open of `W`.

## Main results

* `AlgebraicGeometry.EtaleGaloisCovering.exists_linearEquiv_of_isFiniteProjectiveLocallyConstant`
* `AlgebraicGeometry.EtaleGaloisCovering.finite_projective_of_isFiniteProjectiveLocallyConstant`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u r

namespace AlgebraicGeometry.EtaleGaloisCovering

variable {X : Scheme.{u}} [IrreducibleSpace X] (hX : IsGeometricallyUnibranch X)
  {H : Type*} [Group H] (G : EtaleGaloisCovering X H) {Λ : Type r} [Ring Λ]
  (N : Type (max (u + 1) r)) [AddCommGroup N] [Module Λ N] (ρ : H →* Module.End Λ N)

include hX in
/-- **The descent module of a locally constant sheaf with finite projective values is one of its
values**: it is isomorphic to a finite projective module. -/
theorem exists_linearEquiv_of_isFiniteProjectiveLocallyConstant
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ))
    (hF : Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ X.smallEtaleTopology F)
    (e : F ≅ G.descentSheaf Λ N ρ) :
    ∃ E : ModuleCat.{max (u + 1) r} Λ, Module.Finite Λ E ∧ Module.Projective Λ E ∧
      Nonempty (E ≃ₗ[Λ] N) := by
  obtain ⟨I, V, f, hcov, hV⟩ := hF G.cover
  obtain ⟨x, -⟩ := G.surjective (Classical.arbitrary X)
  obtain ⟨U', g, hg, ⟨y, rfl⟩⟩ :=
    Stacks.EtaleCohomology.exists_mem_range_of_mem_smallEtaleTopology (Sieve.ofArrows V f) hcov x
  obtain ⟨Y, h, g', ⟨i⟩, rfl⟩ := hg
  let vi : (V i).left ⟶ X := (V i).hom
  have : Etale vi := (V i).prop
  obtain ⟨O, hO, hvO, hirr⟩ :=
    exists_isOpen_isPreirreducible_of_etale_of_isGeometricallyUnibranch vi hX (h.left.base y)
  let Oo : (V i).left.Opens := ⟨O, hO⟩
  let T₀ : X.Etale := MorphismProperty.Over.mk ⊤ (Oo.ι ≫ vi) inferInstance
  let T : Over (V i) := Over.mk (MorphismProperty.Over.homMk (A := T₀) (B := V i) Oo.ι rfl trivial)
  have : IrreducibleSpace T.left.left :=
    isIrreducible_iff_irreducibleSpace.mp ⟨⟨_, hvO⟩, hirr⟩
  obtain ⟨E, hEf, hEp, ⟨eE⟩⟩ := hV i
  let eA : (constantSheaf (X.smallEtaleTopology.over G.cover) (ModuleCat.{max (u + 1) r} Λ)).obj
      (ModuleCat.of Λ N) ≅ (X.smallEtaleTopology.overPullback _ G.cover).obj F :=
    G.trivialization Λ N ρ ≪≫ (X.smallEtaleTopology.overPullback _ G.cover).mapIso e.symm
  let φ := eE ≪≫ (Stacks.ConstantSheaf.overPullbackIsoOfMapModule X.smallEtaleTopology (f i) F
    (ModuleCat.of Λ N) eA).symm
  have hφ : Function.Bijective (φ.hom.hom.app (op T)) :=
    (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
  let L₁ := LinearEquiv.ofBijective (((toSheafify (X.smallEtaleTopology.over (V i))
      ((Functor.const (Over (V i))ᵒᵖ).obj E)).app (op T)) ≫ φ.hom.hom.app (op T)).hom
    (hφ.comp (bijective_toSheafify_over_const_app Λ E T))
  let L₂ := LinearEquiv.ofBijective ((toSheafify (X.smallEtaleTopology.over (V i))
      ((Functor.const (Over (V i))ᵒᵖ).obj (ModuleCat.of Λ N))).app (op T)).hom
    (bijective_toSheafify_over_const_app Λ (ModuleCat.of Λ N) T)
  exact ⟨E, hEf, hEp, ⟨L₁.trans L₂.symm⟩⟩

include hX in
/-- **The descent module of a locally constant sheaf with finite projective values is finite
projective.** -/
theorem finite_projective_of_isFiniteProjectiveLocallyConstant
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ))
    (hF : Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ X.smallEtaleTopology F)
    (e : F ≅ G.descentSheaf Λ N ρ) : Module.Finite Λ N ∧ Module.Projective Λ N := by
  obtain ⟨E, hEf, hEp, ⟨L⟩⟩ :=
    G.exists_linearEquiv_of_isFiniteProjectiveLocallyConstant hX N ρ F hF e
  exact ⟨Module.Finite.equiv L, Module.Projective.of_equiv L⟩

end AlgebraicGeometry.EtaleGaloisCovering

end
