module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Coherator
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedQuasicoherent
public import StacksFrontier.CategoryTheory.Triangulated.Quotient

/-!
# The cohomology functors on the derived category with quasi-coherent cohomology

Let `𝒳` be an algebraic stack.  Its derived category with quasi-coherent cohomology sheaves is
the Verdier quotient

`D_QCoh(𝒪_𝒳) = D_{LQCoh^fbc}(𝒪_𝒳) / D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)`

of **Stacks 07B6**.  **Stacks 07B7** names the cohomology functors

`H^i : D_QCoh(𝒪_𝒳) ⟶ QCoh(𝒪_𝒳)`

on it.  They are obtained by descent: on `D_{LQCoh^fbc}(𝒪_𝒳)` one takes the `i`-th cohomology
module, which is locally quasi-coherent with the flat base change property by the very
definition of that subcategory, and then applies the coherator `Q` of **Stacks 0778**, the right
adjoint of `QCoh(𝒪_𝒳) ⊆ LQCoh^fbc(𝒪_𝒳)`.  The resulting functor kills
`D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)`, because the coherator kills exactly the parasitic modules
(**Stacks 0779**), so it inverts the morphisms the Verdier quotient inverts and therefore
factors through `D_QCoh(𝒪_𝒳)`; the factorization is unique up to a unique isomorphism
compatible with it.

## Main definitions

* `AlgebraicGeometry.Stack.cohomologyLocallyQuasicoherentFlatBaseChange`: the functor
  `H^i : D_{LQCoh^fbc}(𝒪_𝒳) ⟶ LQCoh^fbc(𝒪_𝒳)`, the `i`-th cohomology module of a complex,
  restricted to the associated étale site.
* `AlgebraicGeometry.Stack.cohomologyQuasicoherent`: its composite with the coherator, the
  functor `D_{LQCoh^fbc}(𝒪_𝒳) ⟶ QCoh(𝒪_𝒳)` which the quotient descends.
* `AlgebraicGeometry.Stack.cohomologyDerivedCategoryQuasicoherent`: **Stacks 07B7**, the functor
  `H^i : D_QCoh(𝒪_𝒳) ⟶ QCoh(𝒪_𝒳)`, together with
  `AlgebraicGeometry.Stack.cohomologyDerivedCategoryQuasicoherentFac`, the isomorphism
  identifying its composite with the quotient functor with `Q ∘ H^i`.
* `AlgebraicGeometry.Stack.fppfToEtaleModules`: restriction of a module on the fppf site of `𝒳`
  to the associated étale site, and
  `AlgebraicGeometry.Stack.locallyQuasicoherentFlatBaseChangeEtaleModules`, the subcategory
  `LQCoh^fbc(𝒪_𝒳)` of the étale modules as an object property.
* `AlgebraicGeometry.Stack.derivedParasiticSubcategory`: the subcategory
  `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` of `D_{LQCoh^fbc}(𝒪_𝒳)`, the subcategory the Verdier quotient
  divides by.

## Main results

* `AlgebraicGeometry.Stack.isInvertedBy_cohomologyQuasicoherent`: `Q ∘ H^i` inverts every
  morphism of `D_{LQCoh^fbc}(𝒪_𝒳)` whose cone has parasitic cohomology.  This is the step that
  makes the descent possible, and it is the universal property of the Verdier quotient for
  homological functors (**Stacks 05RJ**) applied to the kernel computation of **Stacks 0779**.
* `AlgebraicGeometry.Stack.cohomologyDerivedCategoryQuasicoherent_uniq`: the descended functor is
  unique up to a unique isomorphism compatible with the factorization.
* `CategoryTheory.Localization.existsUnique_isoLift`: the same uniqueness for an arbitrary
  localization, which is what the previous statement specializes.

## Implementation notes

Five inputs are left as hypotheses, each a result of the source this library does not yet have.

*`D_{LQCoh^fbc}(𝒪_𝒳)` is a triangulated subcategory of `D(𝒪_𝒳)`* and *`LQCoh^fbc(𝒪_𝒳)` is
closed under isomorphism* are the derived-category consequences (**Stacks 06UQ**) of
`LQCoh^fbc(𝒪_𝒳)` being a weak Serre subcategory of `Mod(𝒪_𝒳)`, which is **Stacks 0771**.  They
are what gives the ambient category of the quotient its triangulated structure.

*The parasitic modules form a weak Serre class* is **Stacks 0774** (2).  Its closure conditions
under subobjects and extensions are proved in this library, in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/ParasiticSerreSubcategory.lean`; closure
under quotients, clause (2)(a) of the source, is not, which is why the class is assumed here
rather than constructed.

*`H^i : D_{LQCoh^fbc}(𝒪_𝒳) ⟶ LQCoh^fbc(𝒪_𝒳)` composed with the coherator is homological*
(`hhom`) is again a consequence of **Stacks 0771**: the inclusion of a weak Serre subcategory is
exact, cohomology on a derived category is homological, and the coherator is exact by
**Stacks 0779**.

*The coherator kills exactly the parasitic modules* (`hQker`) is **Stacks 0779**, the
identification of the kernel of `Q`.

The coherator itself is the one built in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/Coherator.lean`, and the seven hypotheses it
carries — `hinc`, `hclosed`, `hpres`, `hls`, `hlsD`, `hwp`, `hsep` — are threaded through
unchanged.

Restriction from the fppf site to the étale site leaves the underlying presheaf of modules
untouched, and the presheaf of rings underlying the structure sheaf is the same for all five
topologies of **Stacks 06TP**; so `AlgebraicGeometry.Stack.fppfToEtaleModules` only replaces the
sheaf condition by the weaker one for the coarser topology, and the two readings of
`LQCoh^fbc(𝒪_𝒳)` — as a property of fppf modules and as a property of étale modules — agree on
the nose.

## References

* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 0774](https://stacks.math.columbia.edu/tag/0774)
* [Stacks Project, Tag 0778](https://stacks.math.columbia.edu/tag/0778)
* [Stacks Project, Tag 0779](https://stacks.math.columbia.edu/tag/0779)
* [Stacks Project, Tag 05RJ](https://stacks.math.columbia.edu/tag/05RJ)
* [Stacks Project, Tag 06UQ](https://stacks.math.columbia.edu/tag/06UQ)
* [Stacks Project, Tag 07B6](https://stacks.math.columbia.edu/tag/07B6)
* [Stacks Project, Tag 07B7](https://stacks.math.columbia.edu/tag/07B7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u w t

namespace CategoryTheory.Localization

/-- **A functor factoring through a localization does so uniquely up to a unique isomorphism.**
Given a functor `F` inverting a class of morphisms `W` and a localization functor `L` for `W`,
any functor `G` out of the localization equipped with an isomorphism `α : L ⋙ G ≅ F` is
isomorphic to `CategoryTheory.Localization.lift F hF L` by a unique isomorphism compatible with
`α` and with `CategoryTheory.Localization.fac`.

Existence is `CategoryTheory.Localization.liftNatIso` applied to the identity of `F`, and
uniqueness is `CategoryTheory.Localization.natTrans_ext`: a natural transformation out of a
localization is determined by its values on the image of `L`. -/
theorem existsUnique_isoLift
    {C A E : Type*} [Category C] [Category A] [Category E]
    (W : MorphismProperty C) (F : C ⥤ A) (hF : W.IsInvertedBy F)
    (L : C ⥤ E) [L.IsLocalization W]
    (G : E ⥤ A) (α : L ⋙ G ≅ F) :
    ∃! e : G ≅ Localization.lift F hF L,
      Functor.whiskerLeft L e.hom ≫ (Localization.fac F hF L).hom = α.hom := by
  let _ : Localization.Lifting L W F (Localization.lift F hF L) := ⟨Localization.fac F hF L⟩
  let _ : Localization.Lifting L W F G := ⟨α⟩
  have h : ∀ X, (Localization.liftNatIso L W F F G (Localization.lift F hF L)
      (Iso.refl F)).hom.app (L.obj X) ≫ (Localization.fac F hF L).hom.app X = α.hom.app X := by
    intro X
    change (Localization.liftNatTrans L W F F G (Localization.lift F hF L)
      (Iso.refl F).hom).app (L.obj X) ≫ (Localization.fac F hF L).hom.app X = α.hom.app X
    rw [Localization.liftNatTrans_app L W F F G (Localization.lift F hF L) (Iso.refl F).hom X]
    have hL1 : Localization.Lifting.iso L W F G = α := rfl
    have hL2 : Localization.Lifting.iso L W F (Localization.lift F hF L)
        = Localization.fac F hF L := rfl
    rw [hL1, hL2]
    simp
  refine ⟨Localization.liftNatIso L W F F G (Localization.lift F hF L) (Iso.refl F), ?_, ?_⟩
  · ext X
    simpa using h X
  · intro e' he'
    apply Iso.ext
    apply Localization.natTrans_ext L W
    intro X
    have e1 : e'.hom.app (L.obj X) ≫ (Localization.fac F hF L).hom.app X = α.hom.app X := by
      have := congrArg (fun (τ : L ⋙ G ⟶ F) => τ.app X) he'
      simpa using this
    rw [← cancel_mono ((Localization.fac F hF L).hom.app X), e1, h X]

end CategoryTheory.Localization

namespace DerivedCategoryB

/-- **`D_B(𝒜)` is closed under isomorphism as soon as `B` is.**  An isomorphism of the derived
category induces an isomorphism on every cohomology object. -/
theorem isClosedUnderIsomorphisms_derivedCategoryB
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory.{t} A]
    (B : ObjectProperty A) [B.IsClosedUnderIsomorphisms] :
    (derivedCategoryB B).IsClosedUnderIsomorphisms :=
  ⟨fun e hX n => B.prop_of_iso ((DerivedCategory.homologyFunctor A n).mapIso e) (hX n)⟩

end DerivedCategoryB

namespace AlgebraicGeometry.Stack

open AlgebraicGeometry

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S) (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- **Restriction of a module on the fppf site of an algebraic stack to the associated étale
site.**  The underlying presheaf of modules and the presheaf of rings it is a module over are
unchanged; only the sheaf condition is weakened to the one for the coarser étale topology. -/
def fppfToEtaleModules :
    fppfModules B S hS 𝒳 ⥤
      SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids .etale) where
  obj M := ⟨M.val, M.isSheaf.of_le
    (BigFppfOver.associatedTopology_le_fppf B S hS 𝒳.val.val.p .etale)⟩
  map f := ⟨f.val⟩

/-- The subcategory `LQCoh^fbc(𝒪_𝒳)` of the modules on the associated étale site of an algebraic
stack, as an object property.  Its full subcategory is
`AlgebraicGeometry.Stack.locallyQuasicoherentFlatBaseChangeModules`. -/
abbrev locallyQuasicoherentFlatBaseChangeEtaleModules :
    ObjectProperty (SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids .etale)) :=
  fun F => IsLocallyQuasicoherentWithFlatBaseChange B E h S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids F.val

variable [Abelian (fppfModules B S hS 𝒳)] [HasDerivedCategory.{t} (fppfModules B S hS 𝒳)]

/-- The subcategory `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` of `D_{LQCoh^fbc}(𝒪_𝒳)`, the subcategory
the Verdier quotient of **Stacks 07B6** divides by.  Inside `D_{LQCoh^fbc}(𝒪_𝒳)` the condition
is that all cohomology modules be parasitic, by
`AlgebraicGeometry.Stack.inverseImage_derivedParasiticLocallyQuasicoherentFlatBaseChange`. -/
abbrev derivedParasiticSubcategory : ObjectProperty
    (derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).FullSubcategory :=
  (DerivedCategoryB.derivedCategoryB
      (parasiticModules.{u, w, u} B S hS 𝒳 .fppf)).inverseImage
    (derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).ι

/-- **The cohomology functor `H^i : D_{LQCoh^fbc}(𝒪_𝒳) ⟶ LQCoh^fbc(𝒪_𝒳)`.**  It sends a complex
to the `i`-th cohomology module of the underlying object of `D(𝒪_𝒳)`, restricted to the
associated étale site; that this is locally quasi-coherent with the flat base change property is
the defining property of `D_{LQCoh^fbc}(𝒪_𝒳)` in degree `i`. -/
def cohomologyLocallyQuasicoherentFlatBaseChange (i : ℤ) :
    (derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).FullSubcategory ⥤
      locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS
        𝒳.val.val.p 𝒳.val.isFiberedInGroupoids :=
  (locallyQuasicoherentFlatBaseChangeEtaleModules B E h S hS 𝒳).lift
    ((derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).ι ⋙
      DerivedCategory.homologyFunctor (fppfModules B S hS 𝒳) i ⋙
        fppfToEtaleModules B S hS 𝒳)
    (fun X => X.property i)

section Cohomology

variable [EssentiallySmall.{u} 𝒳.val.val.obj]
  [Abelian (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids)]
  [(locallyQuasicoherentFlatBaseChangeFppfModules B E h S hS 𝒳).IsClosedUnderIsomorphisms]
  [(derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).IsTriangulated]
  [(parasiticModules.{u, w, u} B S hS 𝒳 .fppf).IsWeakSerreClass]
  (hinc : ∀ F : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids,
    IsLocallyQuasicoherentWithFlatBaseChange B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids
      ((FibredSite.toSiteModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids .etale).obj F).val)
  (hclosed : SheafOfModules.ClosedUnderColimitsOfSize.{u, u + 1, u, u, u}
    (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf))
  (hpres : PreservesColimitsOfSize.{u, u}
    (quasicoherentToFlatBaseChange B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids hinc))
  (hls : LocallySmall.{u} (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
    𝒳.val.val.p 𝒳.val.isFiberedInGroupoids))
  (hlsD : LocallySmall.{u} (locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u}
    B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids))
  (hwp : WellPowered.{u} (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
    𝒳.val.val.p 𝒳.val.isFiberedInGroupoids)ᵒᵖ)
  (hsep : HasSeparator (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
    𝒳.val.val.p 𝒳.val.isFiberedInGroupoids))

/-- The coherator `Q : LQCoh^fbc(𝒪_𝒳) ⟶ QCoh(𝒪_𝒳)` of **Stacks 0778** for an algebraic stack,
`AlgebraicGeometry.Stack.flatBaseChangeQuasicoherator` at the structure functor of `𝒳`. -/
abbrev quasicoheratorOfStack :
    locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS
        𝒳.val.val.p 𝒳.val.isFiberedInGroupoids ⥤
      FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids :=
  flatBaseChangeQuasicoherator B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
    hinc hclosed hpres hls hlsD hwp hsep

/-- **The functor `Q ∘ H^i : D_{LQCoh^fbc}(𝒪_𝒳) ⟶ QCoh(𝒪_𝒳)`** which the Verdier quotient of
**Stacks 07B6** descends to the cohomology functor of **Stacks 07B7**: take the `i`-th
cohomology module of a complex and apply the coherator to it. -/
def cohomologyQuasicoherent (i : ℤ) :
    (derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).FullSubcategory ⥤
      FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids :=
  cohomologyLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳 i ⋙
    quasicoheratorOfStack B E h S hS 𝒳 hinc hclosed hpres hls hlsD hwp hsep

/-- **`Q ∘ H^i` inverts the morphisms the Verdier quotient of Stacks 07B6 inverts.**

A morphism of `D_{LQCoh^fbc}(𝒪_𝒳)` is inverted by that quotient when its cone has parasitic
cohomology.  By the kernel computation `hQker` of **Stacks 0779** such a cone is sent to zero by
`Q ∘ H^i` in every degree, so the subcategory `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` lies in the
homological kernel of `Q ∘ H^i`, and the universal property of the Verdier quotient for
homological functors (**Stacks 05RJ**) produces a factorization through the quotient; a functor
isomorphic to one factoring through a localization inverts the same morphisms. -/
theorem isInvertedBy_cohomologyQuasicoherent (i : ℤ)
    (hhom : (cohomologyQuasicoherent B E h S hS 𝒳 hinc hclosed hpres hls hlsD hwp hsep
      i).IsHomological)
    (hQker : ∀ F : locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS
        𝒳.val.val.p 𝒳.val.isFiberedInGroupoids,
      IsZero ((quasicoheratorOfStack B E h S hS 𝒳 hinc hclosed hpres hls hlsD hwp hsep).obj F) ↔
        IsParasitic B S hS 𝒳 .etale F.obj.val) :
    (derivedQuasicoherentW B E h S hS 𝒳).IsInvertedBy
      (cohomologyQuasicoherent B E h S hS 𝒳 hinc hclosed hpres hls hlsD hwp hsep i) := by
  have : (derivedParasiticLocallyQuasicoherentFlatBaseChange B E h S hS
      𝒳).IsClosedUnderIsomorphisms :=
    DerivedCategoryB.isClosedUnderIsomorphisms_derivedCategoryB _
  have : (DerivedCategoryB.derivedCategoryB
      (parasiticModules.{u, w, u} B S hS 𝒳 .fppf)).IsClosedUnderIsomorphisms :=
    DerivedCategoryB.isClosedUnderIsomorphisms_derivedCategoryB _
  have : (DerivedCategoryB.derivedCategoryB
      (parasiticModules.{u, w, u} B S hS 𝒳 .fppf)).IsTriangulated :=
    DerivedCategoryB.derivedCategoryB_isTriangulated _
      (WeakSerre.isWeakSerre_of_isWeakSerreClass _)
  have := hhom
  have hker : derivedParasiticSubcategory B E h S hS 𝒳 ≤
      (cohomologyQuasicoherent B E h S hS 𝒳 hinc hclosed hpres hls hlsD hwp hsep
        i).homologicalKernel := by
    intro X hX n
    exact (hQker _).mpr (((derivedParasiticSubcategory B E h S hS 𝒳).le_shift n X hX) i)
  have hinv : (derivedParasiticSubcategory B E h S hS 𝒳).trW.IsInvertedBy
      (cohomologyQuasicoherent B E h S hS 𝒳 hinc hclosed hpres hls hlsD hwp hsep i) := by
    obtain ⟨H, fac, -, -⟩ := VerdierQuotientUniversalProperty.homological_universal_property
      (derivedParasiticSubcategory B E h S hS 𝒳)
      (cohomologyQuasicoherent B E h S hS 𝒳 hinc hclosed hpres hls hlsD hwp hsep i) hker
    refine (MorphismProperty.IsInvertedBy.iff_of_iso _ fac).mp (fun X Y f hf => ?_)
    have : IsIso ((derivedParasiticSubcategory B E h S hS 𝒳).trW.Q.map f) :=
      Localization.inverts _ _ f hf
    change IsIso (H.map ((derivedParasiticSubcategory B E h S hS 𝒳).trW.Q.map f))
    infer_instance
  rw [show derivedQuasicoherentW B E h S hS 𝒳
      = (derivedParasiticSubcategory B E h S hS 𝒳).trW from by
    rw [derivedQuasicoherentW_eq_trW,
      inverseImage_derivedParasiticLocallyQuasicoherentFlatBaseChange]]
  exact hinv

/-- **Stacks 07B7.** The cohomology functor

`H^i : D_QCoh(𝒪_𝒳) ⟶ QCoh(𝒪_𝒳)`

on the derived category of `𝒪_𝒳`-modules with quasi-coherent cohomology sheaves of an algebraic
stack `𝒳`.  It is the descent through the Verdier quotient of **Stacks 07B6** of the functor
`Q ∘ H^i` on `D_{LQCoh^fbc}(𝒪_𝒳)`, which is possible because that functor inverts the morphisms
the quotient inverts. -/
@[stacks 07B7 "the cohomology functor H^i : D_QCoh(𝒪_𝒳) ⟶ QCoh(𝒪_𝒳)"]
def cohomologyDerivedCategoryQuasicoherent (i : ℤ)
    (hhom : (cohomologyQuasicoherent B E h S hS 𝒳 hinc hclosed hpres hls hlsD hwp hsep
      i).IsHomological)
    (hQker : ∀ F : locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS
        𝒳.val.val.p 𝒳.val.isFiberedInGroupoids,
      IsZero ((quasicoheratorOfStack B E h S hS 𝒳 hinc hclosed hpres hls hlsD hwp hsep).obj F) ↔
        IsParasitic B S hS 𝒳 .etale F.obj.val) :
    derivedCategoryQuasicoherent B E h S hS 𝒳 ⥤
      FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids :=
  Localization.lift (cohomologyQuasicoherent B E h S hS 𝒳 hinc hclosed hpres hls hlsD hwp hsep i)
    (isInvertedBy_cohomologyQuasicoherent B E h S hS 𝒳 hinc hclosed hpres hls hlsD hwp hsep i
      hhom hQker)
    (derivedQuasicoherentW B E h S hS 𝒳).Q

/-- **Stacks 07B7**, the identity defining the cohomology functor: composed with the quotient
functor `D_{LQCoh^fbc}(𝒪_𝒳) ⟶ D_QCoh(𝒪_𝒳)`, the functor `H^i` of **Stacks 07B7** is the functor
`Q ∘ H^i` it descends. -/
@[stacks 07B7 "the identity H^i ∘ (quotient functor) = Q ∘ H^i defining the cohomology functor"]
def cohomologyDerivedCategoryQuasicoherentFac (i : ℤ)
    (hhom : (cohomologyQuasicoherent B E h S hS 𝒳 hinc hclosed hpres hls hlsD hwp hsep
      i).IsHomological)
    (hQker : ∀ F : locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS
        𝒳.val.val.p 𝒳.val.isFiberedInGroupoids,
      IsZero ((quasicoheratorOfStack B E h S hS 𝒳 hinc hclosed hpres hls hlsD hwp hsep).obj F) ↔
        IsParasitic B S hS 𝒳 .etale F.obj.val) :
    toDerivedCategoryQuasicoherent B E h S hS 𝒳 ⋙
        cohomologyDerivedCategoryQuasicoherent B E h S hS 𝒳 hinc hclosed hpres hls hlsD hwp hsep
          i hhom hQker ≅
      cohomologyQuasicoherent B E h S hS 𝒳 hinc hclosed hpres hls hlsD hwp hsep i :=
  Localization.fac _ _ _

/-- **The cohomology functor of Stacks 07B7 is unique up to a unique isomorphism.**  Any functor
out of `D_QCoh(𝒪_𝒳)` whose composite with the quotient functor is identified with `Q ∘ H^i` is
isomorphic to `H^i` by exactly one isomorphism compatible with the two identifications. -/
theorem cohomologyDerivedCategoryQuasicoherent_uniq (i : ℤ)
    (hhom : (cohomologyQuasicoherent B E h S hS 𝒳 hinc hclosed hpres hls hlsD hwp hsep
      i).IsHomological)
    (hQker : ∀ F : locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS
        𝒳.val.val.p 𝒳.val.isFiberedInGroupoids,
      IsZero ((quasicoheratorOfStack B E h S hS 𝒳 hinc hclosed hpres hls hlsD hwp hsep).obj F) ↔
        IsParasitic B S hS 𝒳 .etale F.obj.val)
    (G : derivedCategoryQuasicoherent B E h S hS 𝒳 ⥤
      FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids)
    (α : toDerivedCategoryQuasicoherent B E h S hS 𝒳 ⋙ G ≅
      cohomologyQuasicoherent B E h S hS 𝒳 hinc hclosed hpres hls hlsD hwp hsep i) :
    ∃! e : G ≅ cohomologyDerivedCategoryQuasicoherent B E h S hS 𝒳 hinc hclosed hpres hls hlsD
        hwp hsep i hhom hQker,
      Functor.whiskerLeft (toDerivedCategoryQuasicoherent B E h S hS 𝒳) e.hom ≫
          (cohomologyDerivedCategoryQuasicoherentFac B E h S hS 𝒳 hinc hclosed hpres hls hlsD
            hwp hsep i hhom hQker).hom = α.hom :=
  Localization.existsUnique_isoLift _ _ _ _ G α

end Cohomology

end AlgebraicGeometry.Stack

end
