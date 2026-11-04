module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.QuasiIso
public import StacksFrontier.Homology.KFlat.Bifunctor
public import StacksCore.Tactic.StacksAttribute

/-!
# K-flat complexes preserve quasi-isomorphisms under tensor product

On a ringed site `(C, O)`, taking the total tensor product with a K-flat complex sends
quasi-isomorphisms of complexes of sheaves of `O`-modules to quasi-isomorphisms.

## Main results

* `Stacks.SheafOfModules.KFlatQuasiIso.quasiIso_tensorComplex_of_KFlat`: tensoring with a K-flat
  complex preserves quasi-isomorphisms, expressed by isomorphisms on cohomology sheaves.
* `Stacks.SheafOfModules.KFlatQuasiIso.quasiIso_iff_isIso_leftHomologyMap`: this condition is
  Mathlib's `QuasiIso`.
* `Stacks.SheafOfModules.KFlatQuasiIso.acyclic_mappingCone_tensorComplex_of_KFlat`: tensoring with
  a K-flat complex preserves acyclicity of mapping cones.

## Implementation notes

The tensor product is the canonical sheafified tensor bifunctor
`Stacks.SheafOfModules.Tensor.tensorComplex` (Stacks Tag 06YM), whose map in the first variable is
the induced map of total complexes. K-flatness is `CochainComplex.KFlatBifunctor.KFlat` at the
bifunctor `Stacks.SheafOfModules.Tensor.sheafTensor`, which expresses acyclicity of total tensor
products with acyclic complexes and is Stacks Tag 06YN, to which it unfolds definitionally. A sheaf
of commutative rings on a site specifies the ringed site without choosing a bundled object.

Cohomology is computed as the cokernel of the differential into the kernel of the next
differential (`ShortComplex.leftHomology`), and the tagged preservation theorem uses the induced
maps on those objects directly, which is the Stacks wording.

`HasSheafify` (rather than merely `HasWeakSheafify`) is assumed because it is what makes `Mod(O)`
abelian; abelianness supplies the homology objects the statement names and the biproducts the
mapping cones need.

**Universe constraint.** `Stacks.SheafOfModules.Tensor.sheafTensor` forces the universe of the
sections of the ring sheaf to agree with the universe of the sections of the module sheaves, and
both to be at least the universe of the site; the free parameter above that is `w`. So these are
the ringed-site statements read at a ring-and-module universe `max u v w`, rather than at
independent ring and module universes. The constraint comes from the monoidal structure on
presheaves of modules used by `Stacks.SheafOfModules.Tensor.presheafTensor`.

## References

* [The Stacks Project, Tag 06YP](https://stacks.math.columbia.edu/tag/06YP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u w

namespace Stacks.SheafOfModules.KFlatQuasiIso

/-- Isomorphisms on the usual kernel/cokernel cohomology objects characterize Mathlib's
quasi-isomorphisms whenever the latter's homology instances exist. -/
theorem quasiIso_iff_isIso_leftHomologyMap
    {A : Type u} [Category.{v} A] [HasZeroMorphisms A]
    {F G : CochainComplex A ℤ} (f : F ⟶ G)
    [∀ n, F.HasHomology n] [∀ n, G.HasHomology n] :
    QuasiIso f ↔ ∀ n, IsIso (ShortComplex.leftHomologyMap
      ((HomologicalComplex.shortComplexFunctor A (ComplexShape.up ℤ) n).map f)) :=
  (quasiIso_iff f).trans <| forall_congr' fun n =>
    (quasiIsoAt_iff f n).trans (ShortComplex.quasiIso_iff_isIso_leftHomologyMap' _ _ _)

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (R : Sheaf J CommRingCat.{max u v w})
variable [HasSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
variable [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, max u v w, max u v w} R).Additive]
  [∀ M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, max u v w, max u v w} R).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (ComplexShape.up ℤ)]

/-- Tensoring by a K-flat complex takes a morphism with acyclic cone to a
morphism with acyclic cone. -/
theorem acyclic_mappingCone_tensorComplex_of_KFlat
    (K : CochainComplex (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor R) K)
    {F G : CochainComplex (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ}
    (f : F ⟶ G)
    (hf : (CochainComplex.mappingCone f).Acyclic) :
    (CochainComplex.mappingCone
      (((Stacks.SheafOfModules.Tensor.tensorComplex R).map f).app K)).Acyclic :=
  CochainComplex.KFlatBifunctor.acyclic_mappingCone_of_kFlat
    (Stacks.SheafOfModules.Tensor.sheafTensor R) K hK f hf

/-- Total tensor product with a K-flat complex preserves quasi-isomorphisms:
if the maps on every cohomology sheaf are isomorphisms, so are those induced
by tensoring with `K`. -/
@[stacks 06YP]
theorem quasiIso_tensorComplex_of_KFlat
    (K : CochainComplex (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor R) K)
    {F G : CochainComplex (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ}
    (f : F ⟶ G)
    (hf : ∀ n, IsIso (ShortComplex.leftHomologyMap
      ((HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℤ) n).map f))) :
    ∀ n, IsIso (ShortComplex.leftHomologyMap
      ((HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℤ) n).map
        (((Stacks.SheafOfModules.Tensor.tensorComplex R).map f).app K))) :=
  (quasiIso_iff_isIso_leftHomologyMap _).1
    (CochainComplex.KFlatBifunctor.quasiIso_of_kFlat (Stacks.SheafOfModules.Tensor.sheafTensor R) K
      hK f ((quasiIso_iff_isIso_leftHomologyMap f).2 hf))

/-- Total tensor product with a K-flat complex sends a quasi-isomorphism to a quasi-isomorphism. -/
theorem quasiIso_tensorComplex_of_KFlat_of_quasiIso
    (K : CochainComplex (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor R) K)
    {F G : CochainComplex (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ}
    (f : F ⟶ G) [QuasiIso f] :
    QuasiIso (((Stacks.SheafOfModules.Tensor.tensorComplex R).map f).app K) :=
  CochainComplex.KFlatBifunctor.quasiIso_of_kFlat (Stacks.SheafOfModules.Tensor.sheafTensor R) K hK
    f inferInstance

end Stacks.SheafOfModules.KFlatQuasiIso

end
