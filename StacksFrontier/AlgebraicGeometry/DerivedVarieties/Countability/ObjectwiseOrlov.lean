module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Countability.DerivedEquivalenceFamiliesLimit
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Countability.DerivedEquivalenceKernel
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.ObjectwiseIdentityKernel
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.Linear
public import StacksFrontier.AlgebraicGeometry.Modules.DerivedMonoidal
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComparison

/-!
# Object-wise Orlov: a derived equivalence agrees object-wise with a Fourier-Mukai functor

Let `K` be a field and `X`, `Y` smooth proper `K`-schemes with a `K`-linear exact equivalence
`F : D_perf(𝒪_X) ≌ D_perf(𝒪_Y)`. This file reduces
`AlgebraicGeometry.ObjectwiseFourierMukaiOfEquivalence K` — the statement that `F` agrees object
by object with the Fourier-Mukai functor of a perfect kernel — to the two halves of the source's
argument ([Stacks, Tag 0G0B] and [Stacks, Tag 0G27]), each stated object-wise:

* `AlgebraicGeometry.FourierMukaiAgreesOnZeroDimensional K` (**part A**, the construction of
  [Stacks, Section 0G07]): for a `K`-linear exact fully faithful `F` there is a perfect kernel `P`
  on `X ×_K Y` with `Φ_P(𝓕) ≅ F(𝓕)` for every coherent `𝓕` with zero-dimensional support;
* `AlgebraicGeometry.TwistOfFixingZeroDimensional K` (**part B**, [Stacks, Tag 0G27] read over a
  field over which the automorphism it produces is the identity): a `K`-linear exact
  endofunctor `H` of `D_perf(𝒪_X)` with `H(𝓕) ≅ 𝓕` for every such `𝓕` is object-wise tensoring
  with an invertible object `L` of `D_perf(𝒪_X)`.

Given both, put `H = F⁻¹ ∘ Φ_P`; part B gives `H(E) ≅ E ⊗ L`, so for every perfect `E`,
`F(E) ≅ F(H(E ⊗ L⁻¹)) ≅ Φ_P(E ⊗ L⁻¹) ≅ Φ_{L pr_1^*L⁻¹ ⊗ P}(E)`, the last step being the
compatibility of the derived pullback with the derived tensor product
(`AlgebraicGeometry.fourierMukaiTwistIso`).

## Main definitions

* `AlgebraicGeometry.FourierMukaiAgreesOnZeroDimensional`
* `AlgebraicGeometry.TwistOfFixingZeroDimensional`

## Main results

* `AlgebraicGeometry.fourierMukaiTwistIso`: `Φ_{Lpr_1^*L ⊗ M}(E) ≅ Φ_M(E ⊗ L)`, and
  `AlgebraicGeometry.fourierMukaiTwistNatIso`, the same naturally in `E`.
* `AlgebraicGeometry.fourierMukaiDpullIso`: `Φ_Q ∘ L(a⁻¹)^* ≅ Φ_{L(a × 𝟙)^*Q}` for an automorphism
  `a` of `X` over the base.
* `AlgebraicGeometry.objectwiseFourierMukaiOfEquivalence_of_parts`: the reduction.
* `AlgebraicGeometry.exists_countable_relativeEquivalenceKernels_of_parts`: the statement of
  [Stacks, Tag 0G0Y] over an algebraically closed field from the two halves.

## References

* [Stacks Project, Tag 0G0B](https://stacks.math.columbia.edu/tag/0G0B)
* [Stacks Project, Tag 0G27](https://stacks.math.columbia.edu/tag/0G27)
* [Stacks Project, Tag 0G0Y](https://stacks.math.columbia.edu/tag/0G0Y)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open Stacks.Cohomology.PerfectComplexes (IsPerfect)
open Stacks.Perfect.BoundedLocallyFreeComplexes (PerfectDerivedCategory)

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

/-! ### Twisting a kernel by a pulled-back object -/

section Twist

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- **Twisting the kernel by `L pr_1^*L` twists the argument by `L`**:
`Φ_{L pr_1^*L ⊗ M}(E) ≅ Φ_M(E ⊗ L)`, by associativity of the derived tensor product and the
compatibility of the derived pullback with it. -/
def fourierMukaiTwistIso (M : DerivedCategory (pullback f g).Modules)
    (L E : DerivedCategory X.Modules) :
    (fourierMukai f g ((dtenR _ M).obj ((fourierMukaiPullback f g).obj L))).obj E ≅
      (fourierMukai f g M).obj ((dtenR X L).obj E) :=
  (fourierMukaiPushforward f g).mapIso
    ((@MonoidalCategoryStruct.associator _ _
        (Scheme.Modules.canonicalDerivedMonoidal (pullback f g)).toMonoidalCategoryStruct
        ((fourierMukaiPullback f g).obj E) ((fourierMukaiPullback f g).obj L) M).symm ≪≫
      (dtenR _ M).mapIso
        ((Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso
          (pullback.fst f g).toLRSHom.toShHom).app (E, L)).symm)

/-- **Twisting the kernel by `L pr_1^*L` twists the argument by `L`, naturally**:
`(- ⊗^𝐋 L) ⋙ Φ_M ≅ Φ_{L pr_1^*L ⊗ M}` as functors `D(𝒪_X) ⥤ D(𝒪_Y)`, by the monoidality of the
derived pullback ([Stacks, Tag 079U]) and the associativity of the derived tensor product. -/
def fourierMukaiTwistNatIso (M : DerivedCategory (pullback f g).Modules)
    (L : DerivedCategory X.Modules) :
    dtenR X L ⋙ fourierMukai f g M ≅
      fourierMukai f g ((dtenR _ M).obj ((fourierMukaiPullback f g).obj L)) :=
  letI := Scheme.Modules.canonicalDerivedMonoidal (pullback f g)
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (dpullTensorIso (pullback.fst f g) L)
      (fourierMukaiTensor f g M ⋙ fourierMukaiPushforward f g) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (fourierMukaiPullback f g)
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (tensorRightTensor ((fourierMukaiPullback f g).obj L) M).symm
          (fourierMukaiPushforward f g))

end Twist

/-! ### Changing the kernel along an automorphism of the first factor -/

section Automorphism

variable {U V W : Scheme.{u}}

/-- `L r^* ⋙ L p^* ≅ 𝟭` when `p ≫ r = 𝟙`, by [Stacks, Tag 0D5S] and `L(𝟙)^* ≅ 𝟭`. -/
def dpullCompIsoIdOfCompEqId (p : U ⟶ V) (r : V ⟶ U) (h : p ≫ r = 𝟙 U) :
    dpull r ⋙ dpull p ≅ 𝟭 (DerivedCategory U.Modules) :=
  Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
      p.toLRSHom.toShHom r.toLRSHom.toShHom ≪≫
    eqToIso (by rw [← shHom_comp, h]; rfl) ≪≫
    Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPullbackIdIso U.toRingedSpace

/-- **Derived pullback along an isomorphism of schemes is an equivalence**, with the derived
pullback along the inverse as quasi-inverse. -/
def dpullEquivalence (e : U ≅ V) : DerivedCategory V.Modules ≌ DerivedCategory U.Modules :=
  CategoryTheory.Equivalence.mk (dpull e.hom) (dpull e.inv)
    (dpullCompIsoIdOfCompEqId e.inv e.hom e.inv_hom_id).symm
    (dpullCompIsoIdOfCompEqId e.hom e.inv e.hom_inv_id)

/-- **Derived pullback along an automorphism `e` over `p` does not change the derived direct
image**: `L e^* ⋙ R p_* ≅ R p_*` when `e ≫ p = p`. The unit `𝟭 ⟶ L e^* ⋙ R e_*` of
[Stacks, Tag 079W] is invertible, `L e^*` being an equivalence, and `R e_* ⋙ R p_* ≅ R p_*` by
the composition law of derived direct images. -/
def dpullCompDpushIsoOfIso (e : U ≅ U) (p : U ⟶ W) (h : e.hom ≫ p = p) :
    dpull e.hom ⋙ dpush p ≅ dpush p :=
  haveI : (dpull e.hom).Full := (dpullEquivalence e).fullyFaithfulFunctor.full
  haveI : (dpull e.hom).Faithful := (dpullEquivalence e).fullyFaithfulFunctor.faithful
  let adj : dpull e.hom ⊣ dpush e.hom :=
    @Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction _ _
      e.hom.toLRSHom.toShHom (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
  let c : dpush e.hom ⋙ dpush p ≅ dpush p :=
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCompIso
        e.hom.toLRSHom.toShHom p.toLRSHom.toShHom ≪≫
      eqToIso (by rw [← shHom_comp, h])
  haveI : IsIso adj.unit := Adjunction.unit_isIso_of_L_fully_faithful adj
  Functor.isoWhiskerLeft (dpull e.hom) c.symm ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (asIso adj.unit).symm (dpush p) ≪≫ Functor.leftUnitor _

variable {S X Y : Scheme.{u}} {f : X ⟶ S}

/-- The automorphism `a × 𝟙` of `X ×_S Y` induced by an automorphism `a` of `X` over `S`. -/
def pullbackMapIsoOfIso (g : Y ⟶ S) (a : X ≅ X) (ha : a.hom ≫ f = f) :
    pullback f g ≅ pullback f g where
  hom := pullback.map f g f g a.hom (𝟙 Y) (𝟙 S) (by rw [Category.comp_id, ha])
    (by rw [Category.comp_id, Category.id_comp])
  inv := pullback.map f g f g a.inv (𝟙 Y) (𝟙 S)
    (by rw [Category.comp_id, Iso.eq_inv_comp, ha])
    (by rw [Category.comp_id, Category.id_comp])
  hom_inv_id := by ext <;> simp
  inv_hom_id := by ext <;> simp

/-- **Pulling the argument back along an automorphism of `X` pulls the kernel back along the
induced automorphism of `X ×_S Y`**: `L a^{-1,*} ⋙ Φ_Q ≅ Φ_{L(a × 𝟙)^* Q}` for an automorphism
`a` of `X` over `S`. The two pullbacks to `X ×_S Y` agree by [Stacks, Tag 0D5S], the tensor
product with the kernel moves past `L(a^{-1} × 𝟙)^*` by [Stacks, Tag 079U], and the derived
direct image along `pr_2` absorbs `L(a^{-1} × 𝟙)^*` (`dpullCompDpushIsoOfIso`). -/
def fourierMukaiDpullIso (g : Y ⟶ S) (a : X ≅ X) (ha : a.hom ≫ f = f)
    (Q : DerivedCategory (pullback f g).Modules) :
    dpull a.inv ⋙ fourierMukai f g Q ≅
      fourierMukai f g ((dpull (pullbackMapIsoOfIso g a ha).hom).obj Q) := by
  let k := (pullbackMapIsoOfIso g a ha).symm
  let Q₁ := (dpull (pullbackMapIsoOfIso g a ha).hom).obj Q
  let eQ : (dpull k.hom).obj Q₁ ≅ Q :=
    (dpullCompIsoIdOfCompEqId k.hom k.inv k.hom_inv_id).app Q
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (dpullCompIsoEq (pullback.fst f g) a.inv k.hom (pullback.fst f g)
        (by simp [k, pullbackMapIsoOfIso]))
      (fourierMukaiTensor f g Q ⋙ fourierMukaiPushforward f g) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (fourierMukaiPullback f g)
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (Functor.isoWhiskerLeft (dpull k.hom)
              ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
                (pullback f g).toRingedSpace.sheaf).flip.mapIso
                eQ.symm) ≪≫
            (dpullTensorIso k.hom Q₁).symm) (fourierMukaiPushforward f g) ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (fourierMukaiTensor f g Q₁)
          (dpullCompDpushIsoOfIso k (pullback.snd f g) (by simp [k, pullbackMapIsoOfIso])))

end Automorphism

/-! ### The two halves -/

/-- **Part A: the construction of [Stacks, Section 0G07], object-wise.** For smooth proper
`K`-schemes `X`, `Y` and a `K`-linear exact fully faithful `F : D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)`,
there is a perfect kernel `P` on `X ×_K Y` whose Fourier-Mukai functor agrees with `F` on every
coherent `𝒪_X`-module with zero-dimensional support. -/
def FourierMukaiAgreesOnZeroDimensional (K : Type u) [Field K] : Prop :=
  ∀ A B : Over (Spec (CommRingCat.of K)),
    Smooth A.hom → IsProper A.hom → Smooth B.hom → IsProper B.hom →
      letI : Linear K A.left.Modules := modulesLinear K A
      letI : Linear K B.left.Modules := modulesLinear K B
      ∀ F : PerfectDerivedCategory A.left ⥤ PerfectDerivedCategory B.left, F.Linear K →
        ∀ h : F.CommShift ℤ, (letI := h; F.IsTriangulated) → Nonempty F.FullyFaithful →
          ∃ P : DerivedCategory (pullback A.hom B.hom).Modules,
            IsPerfect (X := (pullback A.hom B.hom).toRingedSpace) P ∧
              ∀ (𝓕 : A.left.Modules), 𝓕.IsCoherent →
                topologicalKrullDim (SheafOfModules.supp 𝓕) = 0 →
                ∀ h𝓕 : IsPerfect (X := A.left.toRingedSpace)
                    ((DerivedCategory.singleFunctor A.left.Modules 0).obj 𝓕),
                  Nonempty ((fourierMukai A.hom B.hom P).obj
                      ((DerivedCategory.singleFunctor A.left.Modules 0).obj 𝓕) ≅
                    (F.obj ⟨_, h𝓕⟩).obj)

/-- **Part B: [Stacks, Tag 0G27], object-wise, with the identity automorphism.** For a smooth
proper `K`-scheme `X`, a `K`-linear exact endofunctor `H` of `D_perf(𝒪_X)` with `H(𝓕) ≅ 𝓕` for
every coherent `𝓕` with zero-dimensional support is object-wise `E ↦ E ⊗^𝐋 L` for an invertible
object `L` of `D_perf(𝒪_X)` (with inverse `L'`). Over an algebraically closed field the
automorphism of [Stacks, Tag 0G27] is the identity ([Stacks, Tag 0G05]), and `L` is an
invertible module placed in degree zero. -/
def TwistOfFixingZeroDimensional (K : Type u) [Field K] : Prop :=
  ∀ A : Over (Spec (CommRingCat.of K)), Smooth A.hom → IsProper A.hom →
    letI : Linear K A.left.Modules := modulesLinear K A
    ∀ H : PerfectDerivedCategory A.left ⥤ PerfectDerivedCategory A.left, H.Linear K →
      ∀ h : H.CommShift ℤ, (letI := h; H.IsTriangulated) →
        (∀ (𝓕 : A.left.Modules), 𝓕.IsCoherent →
          topologicalKrullDim (SheafOfModules.supp 𝓕) = 0 →
          ∀ h𝓕 : IsPerfect (X := A.left.toRingedSpace)
              ((DerivedCategory.singleFunctor A.left.Modules 0).obj 𝓕),
            Nonempty ((H.obj ⟨_, h𝓕⟩).obj ≅
              (DerivedCategory.singleFunctor A.left.Modules 0).obj 𝓕)) →
        ∃ L L' : DerivedCategory A.left.Modules,
          IsPerfect (X := A.left.toRingedSpace) L ∧ IsPerfect (X := A.left.toRingedSpace) L' ∧
            Nonempty ((dtenR A.left L).obj L' ≅
              (DerivedCategory.singleFunctor A.left.Modules 0).obj
                (SheafOfModules.unit A.left.ringCatSheaf)) ∧
            ∀ E : PerfectDerivedCategory A.left,
              Nonempty ((H.obj E).obj ≅ (dtenR A.left L).obj E.obj)

/-! ### The reduction -/

/-- An isomorphism in `D(𝒪_X)` between two perfect objects is an isomorphism in `D_perf(𝒪_X)`. -/
def perfectIsoMk {X : Scheme.{u}} {E E' : PerfectDerivedCategory X} (e : E.obj ≅ E'.obj) :
    E ≅ E' :=
  (ObjectProperty.fullyFaithfulι _).preimageIso e

/-- **`AlgebraicGeometry.ObjectwiseFourierMukaiOfEquivalence` from its two halves.** If over `K`
the construction of [Stacks, Section 0G07] (part A) and [Stacks, Tag 0G27] with the identity
automorphism (part B) hold object-wise, then every `K`-linear exact equivalence of perfect
derived categories of smooth proper `K`-schemes agrees object-wise with a Fourier-Mukai functor
of a perfect kernel. -/
theorem objectwiseFourierMukaiOfEquivalence_of_parts {K : Type u} [Field K]
    (hA : FourierMukaiAgreesOnZeroDimensional K) (hB : TwistOfFixingZeroDimensional K) :
    ObjectwiseFourierMukaiOfEquivalence K := by
  intro A B hAs hAp hBs hBp
  let : Linear K A.left.Modules := modulesLinear K A
  let : Linear K B.left.Modules := modulesLinear K B
  intro e hlin hcs htri
  let := hcs
  let : e.inverse.CommShift ℤ := e.commShiftInverse ℤ
  have : e.CommShift ℤ := e.commShift_of_functor ℤ
  have : e.IsTriangulated := Equivalence.IsTriangulated.mk' e htri
  have : e.functor.Linear K := hlin
  have : IsNoetherian B.left := isNoetherian_of_locallyOfFiniteType B.hom
  have : IsNoetherian A.left := isNoetherian_of_locallyOfFiniteType A.hom
  obtain ⟨P, hP, hPF⟩ := hA A B hAs hAp hBs hBp e.functor hlin hcs htri
    ⟨e.fullyFaithfulFunctor⟩
  let Φ := perfectFourierMukaiOver K A B hP
  have : Φ.Linear K := perfectFourierMukaiOver_linear K A B hP
  let H := Φ ⋙ e.inverse
  have : H.Linear K := inferInstance
  have hfix : ∀ (𝓕 : A.left.Modules), 𝓕.IsCoherent →
      topologicalKrullDim (SheafOfModules.supp 𝓕) = 0 →
      ∀ h𝓕 : IsPerfect (X := A.left.toRingedSpace)
          ((DerivedCategory.singleFunctor A.left.Modules 0).obj 𝓕),
        Nonempty ((H.obj ⟨_, h𝓕⟩).obj ≅
          (DerivedCategory.singleFunctor A.left.Modules 0).obj 𝓕) := by
    intro 𝓕 hcoh hdim h𝓕
    obtain ⟨φ⟩ := hPF 𝓕 hcoh hdim h𝓕
    exact ⟨(ObjectProperty.ι _).mapIso (e.inverse.mapIso (perfectIsoMk φ) ≪≫
      (e.unitIso.app ⟨_, h𝓕⟩).symm)⟩
  obtain ⟨L, L', hL, hL', ⟨eLL'⟩, hHL⟩ := hB A hAs hAp H inferInstance inferInstance
    inferInstance hfix
  refine ⟨(dtenR _ P).obj ((fourierMukaiPullback A.hom B.hom).obj L'), ?_, fun E => ?_⟩
  · exact isPerfect_dtenR _ _
      (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ L' hL') hP
  · let E' : PerfectDerivedCategory A.left :=
      ⟨(dtenR A.left L').obj E.obj, isPerfect_dtenR _ _ E.property hL'⟩
    obtain ⟨φ⟩ := hHL E'
    let := Scheme.Modules.canonicalDerivedMonoidal A.left
    let ψ : (H.obj E').obj ≅ E.obj :=
      φ ≪≫ α_ E.obj L' L ≪≫ whiskerLeftIso E.obj eLL' ≪≫ ρ_ E.obj
    exact ⟨fourierMukaiTwistIso A.hom B.hom P L' E.obj ≪≫
      (ObjectProperty.ι _).mapIso ((e.counitIso.app (Φ.obj E')).symm ≪≫
        e.functor.mapIso (perfectIsoMk ψ))⟩

/-- **The statement of [Stacks, Tag 0G0Y] from parts A and B**, over an algebraically closed
field: the two halves give `AlgebraicGeometry.ObjectwiseFourierMukaiOfEquivalence K`, the
object-wise form of [Stacks, Tag 0G0E] holds over an algebraically closed field
(`AlgebraicGeometry.objectwiseIdentityKernelIsDiagonal`), which together give every derived
equivalence a relative-equivalence kernel, and the countable family is then given by
`exists_countable_relativeEquivalenceKernels_of_derivedEquivalenceHasRelativeKernel`. -/
theorem exists_countable_relativeEquivalenceKernels_of_parts (K : Type u) [Field K]
    [IsAlgClosed K] (hA : FourierMukaiAgreesOnZeroDimensional K)
    (hB : TwistOfFixingZeroDimensional K) :
    ∃ (I : Type (u + 1)) (_ : Countable I)
      (S : I → Over (Spec (.of K)))
      (X Y : (i : I) → Over (S i).left)
      (M : (i : I) → DerivedCategory (pullback (X i).hom (Y i).hom).Modules)
      (_ : ∀ i, LocallyOfFiniteType (S i).hom ∧ QuasiCompact (S i).hom)
      (_ : ∀ i, Smooth (X i).hom ∧ IsProper (X i).hom)
      (_ : ∀ i, Smooth (Y i).hom ∧ IsProper (Y i).hom)
      (_ : ∀ i, IsRelativeEquivalenceKernel (X i).hom (Y i).hom (M i)),
      ∀ (A B : Over (Spec (.of K))),
        Smooth A.hom → IsProper A.hom → Smooth B.hom → IsProper B.hom →
          (letI : Linear K A.left.Modules := modulesLinear K A
           letI : Linear K B.left.Modules := modulesLinear K B
           ∃ e : PerfectDerivedCategory A.left ≌ PerfectDerivedCategory B.left,
             e.functor.Linear K ∧
               ∃ h : e.functor.CommShift ℤ,
                 letI := h
                 e.functor.IsTriangulated) →
            ∃ (i : I) (s : Over.mk (𝟙 (Spec (.of K))) ⟶ S i),
              Nonempty (A ≅ (Over.pullback s.left).obj (X i)) ∧
                Nonempty (B ≅ (Over.pullback s.left).obj (Y i)) :=
  exists_countable_relativeEquivalenceKernels_of_derivedEquivalenceHasRelativeKernel K
    (derivedEquivalenceHasRelativeKernel_of_objectwiseFourierMukai K
      (objectwiseFourierMukaiOfEquivalence_of_parts hA hB))

end AlgebraicGeometry
