module

public import Mathlib.Algebra.Category.Grp.Biproducts
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Limits.FunctorCategory.BinaryBiproducts
public import StacksFrontier.CategoryTheory.Sites.Point.CounitKernel
import StacksCore.Tactic.StacksAttribute

/-!
# The functorial splitting of the stalk of a skyscraper

Let `p` be a point of a topos. On abelian group objects the composite `p⁻¹p_*` is, functorially,
the direct sum of the identity functor and the kernel of its counit: the counit
`p⁻¹p_*A ⟶ A` has a canonical section `η`, which on underlying sets is the canonical map of a
group into the stalk of its skyscraper, and a split epimorphism of abelian group objects
exhibits its source as the biproduct of its target and the kernel.

The decomposition is stated in `AddCommGrpCat`, where biproducts and kernels are available, and
transported back along the canonical equivalence between internal commutative groups in sets
and additive commutative groups; the second summand is then identified with the `Iₚ(A)` of the
definition preceding the source's statement.

## Main definitions

* `Stacks.Topos.Skyscraper.stalkSkyscraperAbFunctor`: `p⁻¹p_*` on abelian group objects.
* `Stacks.Topos.Skyscraper.kernelComplementAbFunctor`: the functorial kernel of its counit.
* `Stacks.Topos.Skyscraper.abelianEta`: the canonical natural section of the counit.

## Main results

* `Stacks.Topos.Skyscraper.stalkSkyscraperAbFunctorIsoBiprod`: the functorial direct-sum
  decomposition, with `stalkSkyscraperAbFunctorIsoBiprod_fst` and
  `stalkSkyscraperAbFunctorIsoBiprod_inl` pinning its projection and inclusion to the counit and
  the canonical section.
* `Stacks.Topos.Skyscraper.abelianEta_hom`: the section is the canonical map on underlying sets.
* `Stacks.Topos.Skyscraper.auxKernelComplementAbFunctorObjIso` and
  `kernelComplementAbFunctorNatIso`: the complementary summand is, naturally, the `Iₚ` of
  `PointOfTopos.kernelComplementOfCounit`.

## Implementation notes

Internal commutative groups in sets are transported to `AddCommGrpCat`, where biproducts and
kernels give the categorical meaning of the direct sum. The first main result states the
functorial decomposition there, with its first inclusion and projection fixed as the canonical
section and the counit, so the splitting cannot be replaced by an unrelated one. The last two
identify the kernel summand — objectwise and then naturally, transported back across the
canonical equivalence — with the kernel used in the definition of `Iₚ(A)`.

## References

* [Stacks Project, Tag 05V7](https://stacks.math.columbia.edu/tag/05V7)
-/

@[expose] public section

namespace Stacks.Topos.Skyscraper

open CategoryTheory CategoryTheory.Limits

universe w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The cartesian monoidal structure on sheaves of sets given by finite products. -/
noncomputable local instance : CartesianMonoidalCategory (Sheaf J (Type w)) :=
  .ofHasFiniteProducts

/-- The symmetric braiding of the cartesian monoidal structure on sheaves of sets. -/
noncomputable local instance : BraidedCategory (Sheaf J (Type w)) :=
  .ofCartesianMonoidalCategory

/-- The endofunctor `p⁻¹p_*` on abelian group objects. -/
noncomputable def stalkSkyscraperAbFunctor (p : PointOfTopos.{w, v, u} J) :
    CategoryTheory.Functor (CommGrp (Type w)) (CommGrp (Type w)) :=
  letI : PreservesFiniteLimits p.inverseImage := p.preservesFiniteLimits
  letI : p.inverseImage.Braided := .ofChosenFiniteProducts _
  letI : PreservesFiniteLimits p.pushforward := p.preservesFiniteLimits_pushforward
  letI : p.pushforward.Braided := .ofChosenFiniteProducts _
  p.pushforward.mapCommGrp ⋙ p.inverseImage.mapCommGrp

/-- The counit `p⁻¹p_* ⟶ 𝟭` on abelian group objects. -/
noncomputable def abelianCounit (p : PointOfTopos.{w, v, u} J) :
    NatTrans (stalkSkyscraperAbFunctor p) (Functor.id (CommGrp (Type w))) :=
  letI : PreservesFiniteLimits p.inverseImage := p.preservesFiniteLimits
  letI : p.inverseImage.Braided := .ofChosenFiniteProducts _
  letI : PreservesFiniteLimits p.pushforward := p.preservesFiniteLimits_pushforward
  letI : p.pushforward.Braided := .ofChosenFiniteProducts _
  p.adj.mapCommGrp.counit

/-- The canonical map from an abelian group into the stalk of its skyscraper,
natural in the abelian group. Its underlying map is the elementwise map of
Stacks Project, Tag 05UX. -/
@[stacks 05V7 "skyscraper_splitting"]
noncomputable def abelianEta (p : PointOfTopos.{w, v, u} J) :
    NatTrans (Functor.id (CommGrp (Type w))) (stalkSkyscraperAbFunctor p) :=
  letI : PreservesFiniteLimits p.inverseImage := p.preservesFiniteLimits
  letI : p.inverseImage.Braided := .ofChosenFiniteProducts _
  letI : PreservesFiniteLimits p.pushforward := p.preservesFiniteLimits_pushforward
  letI : p.pushforward.Braided := .ofChosenFiniteProducts _
  Functor.mapCommGrpIdIso.hom ≫ Functor.mapCommGrpNatTrans p.counitSection ≫
    Functor.mapCommGrpCompIso.hom

/-- The natural section on abelian group objects has the canonical underlying
map of Stacks Project, Tag 05UX. -/
@[stacks 05V7 "skyscraper_splitting"]
theorem abelianEta_hom (p : PointOfTopos.{w, v, u} J)
    (A : CommGrp (Type w)) :
    ((abelianEta p).app A).hom.hom.hom = (p.counitSection.app A.X) :=
  rfl

private theorem abelianCounit_hom (p : PointOfTopos.{w, v, u} J)
    (A : CommGrp (Type w)) :
    ((abelianCounit p).app A).hom.hom.hom = p.adj.counit.app A.X := rfl

/-- The canonical map `A ⟶ p⁻¹p_*A` is a section of the counit `p⁻¹p_*A ⟶ A`. -/
theorem abelianEta_comp_counit_app (p : PointOfTopos.{w, v, u} J)
    (A : CommGrp (Type w)) :
    (abelianEta p).app A ≫ (abelianCounit p).app A = 𝟙 A := by
  apply CommGrp.hom_ext
  ext x
  exact p.counit_app_counitSection_app A.X x

/-- The canonical equivalence from internal commutative groups in sets to
additive commutative groups. -/
@[sga "7 VII 3.5" "partial"]
noncomputable def commGrpAddEquivalence :
    CommGrp (Type w) ≌ AddCommGrpCat :=
  commGrpTypeEquivalenceCommGrp.trans commGroupAddCommGroupEquivalence

/-- The complement `Iₚ` as a functor: it is the kernel of the counit after
transporting internal commutative groups to `AddCommGrpCat`. -/
noncomputable abbrev kernelComplementAbFunctor (p : PointOfTopos.{w, v, u} J) :
    CategoryTheory.Functor (CommGrp (Type w)) AddCommGrpCat :=
  kernel (Functor.whiskerRight (abelianCounit p) commGrpAddEquivalence.functor)

/-- The functorial version of the kernel `Iₚ` defined above, using exactly the
equivalence and kernel occurring in that definition. -/
noncomputable def auxKernelComplementAbFunctor (p : PointOfTopos.{w, v, u} J) :
    CategoryTheory.Functor (CommGrp (Type w)) (CommGrp (Type w)) :=
  kernel (Functor.whiskerRight (abelianCounit p)
    (commGrpTypeEquivalenceCommGrp.functor ⋙ CommGrpCat.toAddCommGrp)) ⋙
      AddCommGrpCat.toCommGrp ⋙ commGrpTypeEquivalenceCommGrp.inverse

-- The universal-property elaboration traverses the functor-category kernel limit.
/-- The binary bicone on `p⁻¹p_*` in `AddCommGrpCat`-valued functors whose inclusions are the
kernel of the counit and the canonical section, and whose projections are the induced retraction
onto the kernel and the counit. -/
noncomputable def stalkSkyscraperAbFunctorSplitBicone
    (p : PointOfTopos.{w, v, u} J) :
    BinaryBicone (kernelComplementAbFunctor p) commGrpAddEquivalence.functor := by
  let ε := Functor.whiskerRight (abelianCounit p) commGrpAddEquivalence.functor
  let η := Functor.whiskerRight (abelianEta p) commGrpAddEquivalence.functor
  have hηε : η ≫ ε = 𝟙 _ := by
    rw [← Functor.whiskerRight_comp]
    change Functor.whiskerRight
      (NatTrans.vcomp (abelianEta p) (abelianCounit p))
      commGrpAddEquivalence.functor = _
    rw [show NatTrans.vcomp (abelianEta p) (abelianCounit p) = NatTrans.id _ from
      NatTrans.ext (funext (abelianEta_comp_counit_app p)), Functor.whiskerRight_id]
    rfl
  let r : stalkSkyscraperAbFunctor p ⋙ commGrpAddEquivalence.functor ⟶ kernel ε :=
    kernel.lift ε (𝟙 _ - ε ≫ η) (by simp [Preadditive.sub_comp, hηε])
  let k : kernel ε ⟶ stalkSkyscraperAbFunctor p ⋙ commGrpAddEquivalence.functor :=
    kernel.ι ε
  refine
    { pt := stalkSkyscraperAbFunctor p ⋙ commGrpAddEquivalence.functor
      fst := r
      snd := ε
      inl := k
      inr := η
      inl_fst := ?_
      inl_snd := kernel.condition ε
      inr_fst := ?_
      inr_snd := hηε }
  all_goals
    apply (cancel_mono k).1
    rw [Category.assoc]
    dsimp [r, k]
    rw [kernel.lift_ι]
    simp [Preadditive.comp_sub, reassoc_of% hηε]

-- The kernel fork comparison expands several layers of functor-category limits.
/-- The bicone `stalkSkyscraperAbFunctorSplitBicone` is a bilimit. -/
noncomputable def stalkSkyscraperAbFunctorSplitBiconeIsBilimit
    (p : PointOfTopos.{w, v, u} J) :
    (stalkSkyscraperAbFunctorSplitBicone p).IsBilimit :=
  BinaryBicone.isBilimitOfKernelInl _ <| by
    convert kernelIsKernel
      (Functor.whiskerRight (abelianCounit p) commGrpAddEquivalence.functor) using 1 <;> rfl

/-- The isomorphism of `p⁻¹p_*` with the biproduct of the identity and the kernel of the counit,
as functors to `AddCommGrpCat`. -/
noncomputable def stalkSkyscraperAbFunctorIsoBiprodAux
    (p : PointOfTopos.{w, v, u} J) :
    Iso (stalkSkyscraperAbFunctor p ⋙ commGrpAddEquivalence.functor)
      (commGrpAddEquivalence.functor ⊞ kernelComplementAbFunctor p) :=
  (biprod.uniqueUpToIso _ _ (stalkSkyscraperAbFunctorSplitBiconeIsBilimit p)).trans
    (biprod.braiding _ _)

/-- **Stacks Project, Tag 05V7.** The decomposition
`p⁻¹p_*A = A ⊕ Iₚ(A)` is functorial in the abelian group `A`. -/
@[stacks 05V7 "skyscraper_splitting"]
noncomputable def stalkSkyscraperAbFunctorIsoBiprod
    (p : PointOfTopos.{w, v, u} J) :
    Iso (stalkSkyscraperAbFunctor p ⋙ commGrpAddEquivalence.functor)
      (commGrpAddEquivalence.functor ⊞ kernelComplementAbFunctor p) :=
  stalkSkyscraperAbFunctorIsoBiprodAux p

/-- The first projection of the splitting is the canonical counit. -/
@[stacks 05V7 "skyscraper_splitting"]
theorem stalkSkyscraperAbFunctorIsoBiprod_fst
    (p : PointOfTopos.{w, v, u} J) :
    (stalkSkyscraperAbFunctorIsoBiprod p).hom ≫ biprod.fst =
      Functor.whiskerRight (abelianCounit p) commGrpAddEquivalence.functor := by
  simp only [stalkSkyscraperAbFunctorIsoBiprod, stalkSkyscraperAbFunctorIsoBiprodAux,
    Iso.trans_hom, biprod.uniqueUpToIso_hom, biprod.braiding]
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (CategoryStruct.comp (biprod.lift
    (stalkSkyscraperAbFunctorSplitBicone p).fst
    (stalkSkyscraperAbFunctorSplitBicone p).snd)) (biprod.lift_fst _ _)).trans ?_
  exact biprod.lift_snd _ _

/-- The first inclusion of the splitting is the canonical map from an
abelian group into the stalk of its skyscraper. -/
@[stacks 05V7 "skyscraper_splitting"]
theorem stalkSkyscraperAbFunctorIsoBiprod_inl
    (p : PointOfTopos.{w, v, u} J) :
    Functor.whiskerRight (abelianEta p) commGrpAddEquivalence.functor ≫
      (stalkSkyscraperAbFunctorIsoBiprod p).hom = biprod.inl := by
  simp only [stalkSkyscraperAbFunctorIsoBiprod, stalkSkyscraperAbFunctorIsoBiprodAux,
    Iso.trans_hom, biprod.uniqueUpToIso_hom, biprod.braiding_hom]
  show (stalkSkyscraperAbFunctorSplitBicone p).inr ≫
    (biprod.lift (stalkSkyscraperAbFunctorSplitBicone p).fst
      (stalkSkyscraperAbFunctorSplitBicone p).snd ≫
      biprod.lift biprod.snd biprod.fst) = _
  apply biprod.hom_ext <;>
    simp only [Category.assoc, biprod.lift_fst, biprod.lift_snd, BinaryBicone.inr_fst,
      BinaryBicone.inr_snd, biprod.inl_fst, biprod.inl_snd]

/-- Objectwise, the auxiliary kernel functor is canonically isomorphic to the
prescribed `Iₚ`. -/
@[stacks 05V7 "skyscraper_splitting"]
noncomputable def auxKernelComplementAbFunctorObjIso
    (p : PointOfTopos.{w, v, u} J)
    (A : CommGrp (Type w)) :
    (auxKernelComplementAbFunctor p).obj A ≅ PointOfTopos.kernelComplementOfCounit p A := by
  letI : PreservesFiniteLimits p.inverseImage := p.preservesFiniteLimits
  letI : p.inverseImage.Braided := .ofChosenFiniteProducts _
  letI : PreservesFiniteLimits p.pushforward := p.preservesFiniteLimits_pushforward
  letI : p.pushforward.Braided := .ofChosenFiniteProducts _
  let δ := Functor.whiskerRight (abelianCounit p)
    (commGrpTypeEquivalenceCommGrp.functor ⋙ CommGrpCat.toAddCommGrp)
  let H : AddCommGrpCat ⥤ CommGrp (Type w) :=
    AddCommGrpCat.toCommGrp ⋙ commGrpTypeEquivalenceCommGrp.inverse
  let f := δ.app A
  let g := CommGrpCat.toAddCommGrp.map <|
    commGrpTypeEquivalenceCommGrp.functor.map ((p.adj.mapCommGrp).counit.app A)
  simpa [auxKernelComplementAbFunctor, PointOfTopos.kernelComplementOfCounit,
    abelianCounit, δ, H, f, g] using
    (H.mapIso (PreservesKernel.iso ((evaluation (CommGrp (Type w)) AddCommGrpCat).obj A) δ) ≪≫
      H.mapIso (kernel.mapIso f g (Iso.refl _) (Iso.refl _) rfl))

/-- The identification of the kernel summand with `Iₚ` is natural, not merely
an objectwise identification. -/
@[stacks 05V7 "skyscraper_splitting"]
noncomputable def kernelComplementAbFunctorNatIso
    (p : PointOfTopos.{w, v, u} J) :
    Iso (kernelComplementAbFunctor p ⋙ commGrpAddEquivalence.inverse)
      (auxKernelComplementAbFunctor p) :=
  Iso.refl _

end Stacks.Topos.Skyscraper
