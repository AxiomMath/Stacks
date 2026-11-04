module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BilinearRingVariableIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorStep4CompositionLaw

/-!
# The composition law for step 4 of the chain of Tag 03EL, solved for the composite

`Stacks.SheafOfModules.pullbackTensorStep4_comp` is the composition law for step 4 of the chain of
bijections of **Stacks 03EL**, and alone among the six it does not have the step at the composite
alone on one side: its conclusion equates

`tensorSheafRestrictScalarsHom (step4CompRingHom φ ψ) … ≫
  (restrictScalars (step4CompRingHom φ ψ)).map (pullbackTensorStep4 (ψ.comp φ) … q)`

with the morphism the same pairing determines over the iterated base ring `φ⁻¹ψ⁻¹O_E`. This file
solves it, which needs exactly two things, both of which are available.

The first is that the comparison of the two tensor products is invertible at the comparison
`Stacks.Sheaves.RingedToposModules.inverseImageRingSheafCompIso` of the two readings of the base
ring: that comparison is an isomorphism of sheaves of rings, and
`Stacks.SheafOfModules.isIso_tensorSheafRestrictScalarsHom` is the invertibility of the lax
structure map of restriction of scalars along an isomorphism. The second is that restriction of
scalars is faithful, which it is for every morphism of sheaves of rings and not only for an
isomorphism, because it acts on a morphism by the very same morphism of underlying sheaves of sets
(`Stacks.Sheaves.RingedToposModules.moduleSheafFunctor_map_restrictScalars_map`) and a morphism of
sheaves of modules is determined by that
(`Stacks.Sheaves.RingedToposModules.hom_ext_moduleSheafFunctor`).

So step 4 at a composite *is* determined by its law, and the implementation notes of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PullbackTensorToposTransition.lean` are wrong to
record the absence of the invertibility as an obstacle to assembling the six laws.

## Main results

* `Stacks.Sheaves.RingedToposModules.restrictScalars_map_injective`: restriction of scalars along
  a morphism of sheaves of rings is faithful.
* `Stacks.SheafOfModules.pullbackTensorStep4_comp_eq`: **the composition law for step 4 determines
  step 4 at the composite.** A candidate morphism which the law's equation holds for *is* step 4
  at the composite.

## References

* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 03D3](https://stacks.math.columbia.edu/tag/03D3)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry CategoryTheory.Sheaf
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe w w' w'' v u v' u' v'' u''

namespace Stacks.Sheaves.RingedToposModules

section Faithful

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  {R R' : Sheaf J RingCat.{w}}

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- **Restriction of scalars along a morphism of sheaves of rings is faithful.** It acts on a
morphism of sheaves of modules by the very same morphism of underlying sheaves of sets
(`Stacks.Sheaves.RingedToposModules.moduleSheafFunctor_map_restrictScalars_map`), and a morphism
of sheaves of modules is determined by that
(`Stacks.Sheaves.RingedToposModules.hom_ext_moduleSheafFunctor`). No invertibility of the
morphism of sheaves of rings is needed. -/
lemma restrictScalars_map_injective (u : R ⟶ R') {M N : SheafOfModules.{w} R'} {k k' : M ⟶ N}
    (h : (SheafOfModules.restrictScalars u).map k = (SheafOfModules.restrictScalars u).map k') :
    k = k' :=
  hom_ext_moduleSheafFunctor
    ((moduleSheafFunctor_map_restrictScalars_map u k).symm.trans
      ((congrArg (Sheaf.moduleSheafFunctor R).map h).trans
        (moduleSheafFunctor_map_restrictScalars_map u k')))

end Faithful

end Stacks.Sheaves.RingedToposModules

namespace Stacks.SheafOfModules

section Step4

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  {Z : RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (φ : AlgebraicGeometry.RingedToposHom X Y) (ψ : AlgebraicGeometry.RingedToposHom Y Z)
  (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- **The composition law for step 4 of the chain of Tag 03EL determines step 4 at the
composite.** Let `φ : (Sh(C), O_C) ⟶ (Sh(D), O_D)` and `ψ : (Sh(D), O_D) ⟶ (Sh(E), O_E)` be
morphisms of ringed topoi, let `F` and `G` be sheaves of `O_E`-modules, let `N` be a sheaf of
`O_C`-modules and let `q` be a bilinear pairing of `(ψ ∘ φ)⁻¹F` and `(ψ ∘ φ)⁻¹G` over
`(ψ ∘ φ)⁻¹O_E`. A morphism `m` out of their tensor product over that ring which satisfies the
equation of `Stacks.SheafOfModules.pullbackTensorStep4_comp` *is* `pullbackTensorStep4` at the
composite.

This is what makes step 4 usable in an assembly of the six composition laws of the chain of
Stacks 03EL: the law itself has the step at the composite under
`tensorSheafRestrictScalarsHom … ≫ (restrictScalars …).map (-)`, and that is an isomorphism
followed by a faithful functor. -/
theorem pullbackTensorStep4_comp_eq
    (F G : SheafOfModules.{w''} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
    (q : { q : Sheaf.moduleSheaf (step4CompRingSheaf φ ψ) (step4CompSource φ ψ F) ⨯
            Sheaf.moduleSheaf (step4CompRingSheaf φ ψ) (step4CompSource φ ψ G) ⟶
          Sheaf.moduleSheaf (step4CompRingSheaf φ ψ) (step3CompValues φ ψ N) //
        IsBilinearPairing (step4CompRingSheaf φ ψ) q })
    {m : inverseImageTensorSheaf (ψ.comp φ).toModulesHom (step4CompSource φ ψ F)
        (step4CompSource φ ψ G) ⟶
      (SheafOfModules.restrictScalars (ψ.comp φ).toModulesHom.fSharpInverseImage).obj N}
    (hm : tensorSheafRestrictScalarsHom (step4CompRingHom φ ψ) (step4CompSource φ ψ F)
            (step4CompSource φ ψ G) ≫
          (SheafOfModules.restrictScalars (step4CompRingHom φ ψ)).map m =
        bilinearEquivTensorSheafHom (hA := isSheaf_step4CompRing φ ψ)
          (F := (SheafOfModules.restrictScalars (step4CompRingHom φ ψ)).obj
            (step4CompSource φ ψ F))
          (G := (SheafOfModules.restrictScalars (step4CompRingHom φ ψ)).obj
            (step4CompSource φ ψ G))
          (N := (SheafOfModules.restrictScalars (step4CompRingHom φ ψ)).obj
            (step3CompValues φ ψ N))
          ⟨q.1, q.2.restrictScalars (step4CompRingHom φ ψ)⟩) :
    pullbackTensorStep4 (ψ.comp φ).toModulesHom F G N q = m := by
  have : IsIso (step4CompRingHom φ ψ) :=
    Iso.isIso_hom (inverseImageRingSheafCompIso φ.toToposHom ψ.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
  have : IsIso (tensorSheafRestrictScalarsHom (step4CompRingHom φ ψ) (step4CompSource φ ψ F)
      (step4CompSource φ ψ G)) :=
    isIso_tensorSheafRestrictScalarsHom (step4CompRingHom φ ψ) (step4CompSource φ ψ F)
      (step4CompSource φ ψ G)
  have : Epi (tensorSheafRestrictScalarsHom (step4CompRingHom φ ψ) (step4CompSource φ ψ F)
      (step4CompSource φ ψ G)) := IsIso.epi_of_iso _
  refine restrictScalars_map_injective (step4CompRingHom φ ψ) ((cancel_epi
    (tensorSheafRestrictScalarsHom (step4CompRingHom φ ψ) (step4CompSource φ ψ F)
      (step4CompSource φ ψ G))).1 ?_)
  exact (pullbackTensorStep4_comp φ ψ N F G q).trans hm.symm

end Step4

end Stacks.SheafOfModules

end
