module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BilinearRingVariable
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectImageCompositionLaw
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorStep3CompositionLaw
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackHomAlgebra

/-!
# The composition law for step 4 of the chain of Tag 03EL

`Stacks.SheafOfModules.pullbackTensorStep4` is the fourth link of the chain of bijections of
Tag 03EL, the universal property of the tensor product sheaf over the inverse image of the
structure sheaf of the target:

`Bilin_{χ⁻¹O_E}(χ⁻¹F × χ⁻¹G, N|) = Hom_{χ⁻¹O_E}(χ⁻¹F ⊗_{χ⁻¹O_E} χ⁻¹G, N|)`.

As for step 2, there is only *one* universal property here and nothing for a composite to
compose: a morphism of ringed topoi `χ` enters step 4 through the sheaf of rings `χ⁻¹O_E`, the
two inverse-image modules and the restricted sheaf of values, all in the single spelling `χ`.
Step 4 for `φ` and step 4 for `ψ` are bijections between four unrelated types — the target of
the one is a module hom-set and the source of the other a set of bilinear pairings — so they
never compose, exactly as the implementation notes of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorStep3CompositionLaw` record for
step 3.

What a composite does supply is a *comparison of the base rings*. Unlike step 2, whose sheaf of
rings is the structure sheaf of the target and is therefore shared by a composite and its second
factor, the base ring of step 4 for `ψ ∘ φ` is `(ψ ∘ φ)⁻¹O_E`, and the ring a two-stage
construction produces is the iterated inverse image `φ⁻¹ψ⁻¹O_E`. Those are two different sheaves
of rings on the same underlying sheaf of sets
(`Stacks.Sheaves.RingedToposModules.inverseImageRingSheafCompIso`), and the composition law for
step 4 is the statement that the one universal property is compatible with that comparison.
That is what is proved here.

## Main definitions

* `Stacks.SheafOfModules.step4CompRing`: the iterated inverse image `φ⁻¹ψ⁻¹O_E`, as a presheaf
  of commutative rings — the form in which the universal property of the tensor product sheaf
  takes its base ring.
* `Stacks.SheafOfModules.step4CompRingHom`: the comparison `φ⁻¹ψ⁻¹O_E ⟶ (ψ ∘ φ)⁻¹O_E` of the two
  readings of the base ring, read between those two presentations.
* `Stacks.SheafOfModules.step4CompSource`: the inverse image along the composite of a sheaf of
  `O_E`-modules, the source module step 4 for the composite consumes.

## Main results

* `Stacks.SheafOfModules.pullbackTensorStep4_comp`: **the composition law for step 4.** Step 4
  for a composite `ψ ∘ φ`, restricted along the comparison of the two readings of the base ring
  and precomposed with the comparison of the two tensor products, is the universal property over
  the iterated base ring `φ⁻¹ψ⁻¹O_E` applied to the *same* bilinear pairing.

## Implementation notes

*Where the content is.* All of it is in the ring variable of the universal property of the
tensor product sheaf, which
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BilinearRingVariable` supplies as
`Stacks.SheafOfModules.bilinearEquivTensorSheafHom_restrictScalars`; the law below is that lemma
at the comparison `Stacks.SheafOfModules.step4CompRingHom`. Nothing of the chain of Tag 03EL
enters the proof, which is why the law holds for an arbitrary morphism of sheaves of rings and
is specialized here only to the one the chain needs.

*The two presentations of the base ring.* The universal property of the tensor product sheaf is
stated for a sheaf of rings presented as a presheaf of *commutative* rings with a sheaf condition
on its underlying presheaf of rings, because that is the only form in which an inverse image of
a structure sheaf is available (see the implementation notes of
`Stacks.SheafOfModules.inverseImageTensorSheaf`). For the base ring of the composite that
presentation is `Stacks.Sheaves.RingedToposModules.inverseImageStructureCommRing`; for the
iterated one it has to be built, which is `step4CompRing` below, and the commutativity it asks
for is `Stacks.Sheaves.ToposPullback.pullback_sections_mul_comm` — the sections of an inverse
image commute as soon as those of the original do. Both presentations agree with the geometric
spelling `inverseImageRingSheaf` by `rfl`
(`Stacks.Sheaves.RingedToposModules.pullbackRingSheaf_eq_commRingSheaf`), so the comparison of
the two readings needs no transport beyond a type ascription.

*The underlying morphism of topoi of the composite.* As in the laws for steps 2 and 3, the
composite is the two-field `AlgebraicGeometry.RingedToposHom.comp` of Stacks 01D3 (3) read
through `AlgebraicGeometry.RingedToposHom.toModulesHom`; the four-field morphism of ringed topoi
the chain is stated at has no composition of its own. Both
`AlgebraicGeometry.RingedToposHom.comp_toToposHom` and
`AlgebraicGeometry.RingedToposHom.toModulesHom_toToposHom` hold by `rfl`, so the two spellings
`(ψ ∘ φ)⁻¹` and `φ⁻¹ ∘ ψ⁻¹` of the inverse image of *sheaves of sets* agree on the nose and only
the transported ring structures differ.

## References

* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry CategoryTheory.Sheaf
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace Stacks.SheafOfModules

universe w w' w'' v u v' u' v'' u''

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

/-- The base ring of step 4 of the chain of Tag 03EL, for a morphism of ringed topoi presented
as a composite: the inverse image `(ψ ∘ φ)⁻¹O_E` of the structure sheaf of the target. -/
abbrev step4CompRingSheaf : Sheaf X.J RingCat.{w} :=
  inverseImageRingSheaf (ψ.toToposHom.comp φ.toToposHom)
    (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)

/-- The *iterated* inverse image `φ⁻¹ψ⁻¹O_E` of the structure sheaf of the target, as a presheaf
of commutative rings on the source site. This is the base ring a two-stage construction produces,
and it is not `Stacks.SheafOfModules.step4CompRingSheaf`: the underlying sheaf of sets is the
same, the transported ring structure is not.

The commutativity of its sections is
`Stacks.Sheaves.ToposPullback.pullback_sections_mul_comm` applied twice. -/
abbrev step4CompRing : X.Cᵒᵖ ⥤ CommRingCat.{w} :=
  inverseImageCommRingPresheaf X.J φ.toToposHom.inverseImage
    (inverseImageRingSheaf ψ.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
    (pullback_sections_mul_comm Y.J ψ.toToposHom.inverseImage (ringSheaf_mul_comm Z))

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The iterated inverse image of the structure sheaf of the target is a sheaf, read as the sheaf
condition on the underlying presheaf of rings of a presheaf of commutative rings. -/
lemma isSheaf_step4CompRing :
    Presheaf.IsSheaf X.J
      (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf (step4CompRing φ ψ)) :=
  (inverseImageRingSheaf φ.toToposHom
    (inverseImageRingSheaf ψ.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))).property

/-- **The comparison of the two readings of the base ring of step 4**, read between the two
presentations as presheaves of commutative rings that the universal property of the tensor
product sheaf requires. It is
`Stacks.Sheaves.RingedToposModules.inverseImageRingSheafCompIso`, and it is the identity on
underlying sheaves of sets. -/
abbrev step4CompRingHom :
    commRingSheaf X.J (step4CompRing φ ψ) (isSheaf_step4CompRing φ ψ) ⟶
      commRingSheaf X.J (inverseImageStructureCommRing (ψ.comp φ).toModulesHom)
        (isSheaf_inverseImageStructureCommRing (ψ.comp φ).toModulesHom) :=
  (inverseImageRingSheafCompIso φ.toToposHom ψ.toToposHom
    (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).hom

/-- The inverse image along the composite of a sheaf of `O_E`-modules: one of the two source
modules step 4 for the composite consumes. -/
abbrev step4CompSource (F : SheafOfModules.{w''} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) :
    SheafOfModules.{w} (step4CompRingSheaf φ ψ) :=
  (inverseImageModules (ψ.toToposHom.comp φ.toToposHom)
    (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).obj F

/-- **The composition law for step 4 of the chain of Tag 03EL.** Let
`φ : (Sh(C), O_C) ⟶ (Sh(D), O_D)` and `ψ : (Sh(D), O_D) ⟶ (Sh(E), O_E)` be morphisms of ringed
topoi, let `F` and `G` be sheaves of `O_E`-modules and `N` a sheaf of `O_C`-modules. Step 4 for
the composite sends a bilinear pairing `q` of `(ψ ∘ φ)⁻¹F` and `(ψ ∘ φ)⁻¹G` over
`(ψ ∘ φ)⁻¹O_E` to a morphism out of their tensor product over that ring. Restricting that
morphism along the comparison `φ⁻¹ψ⁻¹O_E ⟶ (ψ ∘ φ)⁻¹O_E` of the two readings of the base ring,
and precomposing with the comparison of the two tensor products, gives the morphism that the
*same* pairing `q` determines by the universal property over the iterated base ring.

This is the honest shape of a composition law for step 4: the implementation notes record why it
is *not* an equation between step 4 for `φ` and step 4 for `ψ`, which do not compose, and why —
unlike step 2 — a comparison of base rings has to appear.

It is `Stacks.SheafOfModules.bilinearEquivTensorSheafHom_restrictScalars` read at that
comparison. -/
theorem pullbackTensorStep4_comp
    (F G : SheafOfModules.{w''} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
    (q : { q : Sheaf.moduleSheaf (step4CompRingSheaf φ ψ) (step4CompSource φ ψ F) ⨯
            Sheaf.moduleSheaf (step4CompRingSheaf φ ψ) (step4CompSource φ ψ G) ⟶
          Sheaf.moduleSheaf (step4CompRingSheaf φ ψ) (step3CompValues φ ψ N) //
        IsBilinearPairing (step4CompRingSheaf φ ψ) q }) :
    tensorSheafRestrictScalarsHom (step4CompRingHom φ ψ) (step4CompSource φ ψ F)
          (step4CompSource φ ψ G) ≫
        (SheafOfModules.restrictScalars (step4CompRingHom φ ψ)).map
          (pullbackTensorStep4 (ψ.comp φ).toModulesHom F G N q) =
      bilinearEquivTensorSheafHom (hA := isSheaf_step4CompRing φ ψ)
        (F := (SheafOfModules.restrictScalars (step4CompRingHom φ ψ)).obj
          (step4CompSource φ ψ F))
        (G := (SheafOfModules.restrictScalars (step4CompRingHom φ ψ)).obj
          (step4CompSource φ ψ G))
        (N := (SheafOfModules.restrictScalars (step4CompRingHom φ ψ)).obj
          (step3CompValues φ ψ N))
        ⟨q.1, q.2.restrictScalars (step4CompRingHom φ ψ)⟩ :=
  bilinearEquivTensorSheafHom_restrictScalars (step4CompRingHom φ ψ) (step4CompSource φ ψ F)
    (step4CompSource φ ψ G) q

end Step4

end Stacks.SheafOfModules

end
