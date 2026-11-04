module

public import StacksFrontier.AlgebraicGeometry.Duality.ParametrizedAdjointUniqueness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackExistence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorSheafHomAdjunctionSlot
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomModelIndependence
import StacksCore.Tactic.StacksAttribute

/-!
# The derived pushforward of an internal hom out of a derived pullback

Let `f : (Sh(C), O') ⟶ (Sh(D), O)` be a morphism of ringed topoi and let `A` be an object of
`D(O)`.  This file proves the canonical isomorphism

`Rf_* RSheafHom_{O'}(Lf^*A, M) ≅ RSheafHom_O(A, Rf_*M)`

in `D(O)`, naturally in `M` in `D(O')` **and in `A` in `D(O)`**, for **arbitrary** `A` and `M`:
no perfectness, no duals, no boundedness and no finiteness.

## The proof

Both sides are right adjoints, and the two left adjoints are isomorphic by Stacks 07A4.

Writing `⊗` for the derived tensor product of Stacks 06YU and `RSheafHom` for the derived
internal hom of Stacks 0A97, the tensor–internal-hom adjunction of Stacks 08J8 and the derived
adjunction of Stacks 07A6 compose in the two possible orders:

* `Lf^* ⋙ (Lf^*A ⊗ -) ⊣ RSheafHom_{O'}(Lf^*A, -) ⋙ Rf_*`, and
* `(A ⊗ -) ⋙ Lf^* ⊣ Rf_* ⋙ RSheafHom_O(A, -)`.

The right adjoints are the two sides of the displayed formula, read as functors
`D(O') ⟶ D(O)`.  The left adjoints send `N` to `Lf^*A ⊗ Lf^*N` and to `Lf^*(A ⊗ N)`, so they
are isomorphic by Stacks 07A4 with its first tensor slot fixed at `A`; transporting the second
adjunction along that isomorphism makes the two adjunctions share a left adjoint, and
`CategoryTheory.Adjunction.rightAdjointUniq` produces the isomorphism of the right ones.

## Main definitions

* `Stacks.Cohomology.DerivedInternalHomPushforward.derivedPullbackTensorIsoFixedSource`:
  Stacks 07A4 with its first tensor slot fixed, `Lf^*(A ⊗ -) ≅ Lf^*A ⊗ Lf^*(-)`.
* `Stacks.Cohomology.DerivedInternalHomPushforward.derivedPullbackTensorSheafHomAdjunction` and
  `derivedTensorPullbackSheafHomAdjunction`: the two composite adjunctions above.
* `Stacks.Cohomology.DerivedInternalHomPushforward.derivedPushforwardSheafHomIso`: **the
  isomorphism `Rf_* RSheafHom_{O'}(Lf^*A, M) ≅ RSheafHom_O(A, Rf_*M)`**, as an isomorphism of
  functors `D(O') ⟶ D(O)`, i.e. naturally in `M`.
* `Stacks.Cohomology.DerivedInternalHomPushforward.derivedPushforwardSheafHomObjIso`: its value
  at an object `M`, for clients that want the plain isomorphism of objects of `D(O)`.
* `AlgebraicGeometry.RingedSite.derivedTensorSheafHomParametrizedAdjunction`: Stacks 08J8 as an
  **adjunction with a parameter**, `A ⊗^𝐋_O - ⊣ RSheafHom(A, -)` naturally in `A`.
* `Stacks.Cohomology.DerivedInternalHomPushforward.derivedPushforwardSheafHomBifunctorIso`:
  **the same isomorphism as an isomorphism of bifunctors `D(O)ᵒᵖ ⥤ D(O') ⥤ D(O)`**, i.e.
  naturally in `A` as well as in `M`.
* `Stacks.Cohomology.DerivedInternalHomPushforward.derivedPushforwardSheafHomIsoOfObj`: its value
  at a fixed `M`, as an isomorphism of functors of `A`; composed with `S.op` for a system
  `S : J ⥤ D(O)` this is the isomorphism of the two towers that a derived-limit argument
  consumes.

## Main results

* `Stacks.Cohomology.DerivedInternalHomPushforward.derivedPushforwardSheafHomObjIso_naturality`:
  the naturality square of the isomorphism in `M`, spelled out at objects.
* `Stacks.Cohomology.DerivedInternalHomPushforward.unit_derivedPushforwardSheafHomIso` and
  `derivedPushforwardSheafHomIso_counit`: the isomorphism carries the unit of the first
  adjunction to the unit of the second and the counit of the second to the counit of the first —
  which is what `CategoryTheory.Adjunction.rightAdjointUniq` is, and what pins the isomorphism
  down rather than leaving it an unconstrained map between the two objects.
* `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_naturality_snd`: **Stacks 08J8 is natural in
  its middle object**, the clause of its functoriality that
  `StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryTargetNaturality` leaves
  out.  It is what makes the formula natural in `A`.
* `AlgebraicGeometry.RingedSite.derivedCurryIso_natural_snd`: the middle-variable square of
  Stacks 08J9, the companion of `derivedCurryIso_natural_fst` and
  `derivedCurryIso_natural_thd`.

## What is not claimed

No tag is attached.  The displayed formula is not a Stacks tag: Section 21.35 (Stacks 08J7)
states the tensor–internal-hom bijection (Stacks 08J8), the currying isomorphism
(Stacks 08J9), the comparison maps of Remarks 21.35.10–21.35.12 — including
`Lh^* RSheafHom(K, L) ⟶ RSheafHom(Lh^*K, Lh^*L)`, which is Stacks 08JF and is proved in
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedPullbackOfInternalHom` — but not
this adjoint formula, and the parallel section for ringed spaces (Section 20.42) does not either.

Naturality in `A` is claimed, and proved: a morphism `A' ⟶ A` moves both the left and the right
adjoint of each of the two composite adjunctions, so it is not a naturality square for one
adjunction but a compatibility of four, and what organises it is the notion of an adjunction
with a parameter, `CategoryTheory.ParametrizedAdjunction`.  The two composite adjunctions are
families over `A` satisfying its naturality axiom, and
`Stacks.Duality.parametrizedRightAdjointUniq` of
`StacksFrontier.AlgebraicGeometry.Duality.ParametrizedAdjointUniqueness` — together with the three
ways of building such a family out of an ordinary adjunction that the same file supplies — then
produces the isomorphism of bifunctors.  The one input that needs proving here is the naturality
of Stacks 08J8 in its middle object, `derivedCurryHomEquiv_naturality_snd` below, which
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryTargetNaturality` records
as not treated there.

## Implementation notes

*The isomorphism is built without forming an equivalence of morphism groups.*  The adjunction
of Stacks 08J8 is taken as
`AlgebraicGeometry.RingedSite.interfaceDerivedTensorSheafHomAdjunction` and the adjunction of
Stacks 07A6 as
`Stacks.Cohomology.DerivedPullbackOnRingedTopoi.derivedAdjunction`; the isomorphism is then
`CategoryTheory.Adjunction.comp`, `CategoryTheory.Adjunction.ofNatIsoLeft` and
`CategoryTheory.Adjunction.rightAdjointUniq`, which see only the bundled adjunctions and an
isomorphism of plain functor composites.  No new `Equiv` or `AddEquiv` of `DerivedCategory`
morphism groups is built or coerced along that route, which is the step recorded as exhausting
the recursion depth in the implementation notes of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedPullbackOfInternalHom`.  The
bijection `derivedCurryHomEquiv` of Stacks 08J8 does appear, but only inside the middle
naturality clause and in `derivedTensorSheafHomAdjunction_homEquiv`, which reads the hom-set
bijection of that adjunction off it — in exactly the shape in which
`DerivedCurryTargetNaturality` already reads its counit, and with the heavy steps split into
their own declarations so that no one of them has to normalise the whole composite.

*Which derived tensor product.*  Stacks 07A4 is stated over
`Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor`, and
`interfaceDerivedTensorSheafHomAdjunction` is the adjunction of Stacks 08J8 read over that same
bifunctor — that is what the `interface` prefix of its name records — so the two meet with no
bridging isomorphism of tensor products.

*Fixing a tensor slot.*  Stacks 07A4 is stated between the two uncurried bifunctors on
`D(O) × D(O)`, so naturality in both variables is part of its type.  Fixing the first slot is
`CategoryTheory.NatIso.ofComponents` on its components at `(A, -)`, whose naturality square is
its own square at a morphism `(𝟙 A, g)` with the two identities cancelled; currying it back into
an isomorphism of bifunctors is the same construction with the square at `(a, 𝟙 N)`.

*The middle naturality of Stacks 08J8.*  It is proved here rather than imported.  The
development states the source and target clauses in `DerivedCurrySourceNaturality` and
`DerivedCurryTargetNaturality`, which is the one the adjunction of Stacks 08J8 is built in, and
states the middle clause a second time in `DerivedCurryingHomNaturality`, as
`derivedCurryHomEquiv_naturality_middle`.  This file does not import that module, and proves the
clause by the same route the other two clauses take: the object-level square of Stacks 08J9
transported at both ends by the naturality of Stacks 08JA,
`derivedSheafHomGlobalSectionsEquiv_naturality`.

*A ringed topos and a ringed site carry the same data*, and the adjunction of Stacks 08J8 is
stated for a ringed site, so it is read off the presenting ringed sites
`AlgebraicGeometry.RingedTopos.toRingedSite`, exactly as in
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedPullbackOfInternalHom`.  Nothing
is transported: the two structures have the same structure sheaf, hence the same sheaf of rings
and the same category of modules.

*Universes.*  Both ringed topoi are taken at `RingedTopos.{u, u, u}`, the narrowing carried by
Stacks 07A4 and by Stacks 08J8 in this development, which inherit it from the K-flat resolutions
of Stacks 06YS behind the derived tensor product of Stacks 06YU.  The derived categories' own
hom universe is the standard one.

*The hypotheses.*  `hmos`, that the continuous functor presenting `f` is a morphism of sites, is
what makes `f` a morphism of ringed *topoi* at all — `AlgebraicGeometry.RingedToposSiteHom` asks
only for continuity — and is carried in the same shape by Stacks 07A4, 07A6 and 08JF here.  The
`HasLeftDerivedFunctor` binder is a `Prop` class without which `Lf^*` cannot be written down,
and it is discharged for every morphism of ringed topoi by
`Stacks.Cohomology.DerivedPullbackOnRingedTopoi.hasLeftDerivedFunctor_pullbackOnHomotopy`.

## References

* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks Project, Tag 0A97](https://stacks.math.columbia.edu/tag/0A97)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Cohomology.DerivedPullbackOnRingedTopoi
open Stacks.DerivedTensor.RingedSite
open Stacks.Cohomology.ModuleSections

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.Cohomology.DerivedInternalHomPushforward

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]
  (f : RingedToposSiteHom X Y)
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))]
  (hmos : f.u.IsMorphismOfSites Y.J X.J)
  (A : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))

/-! ### Stacks 07A4 with the first tensor slot fixed -/

/-- **Stacks 07A4 with its first tensor slot fixed at `A`**: the isomorphism of functors
`D(O) ⟶ D(O')`

`Lf^*(A ⊗^𝐋_O -) ≅ Lf^*A ⊗^𝐋_{O'} Lf^*(-)`.

Stacks 07A4, `Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso`, is an
isomorphism of the two uncurried bifunctors on `D(O) × D(O)`; this is its family of components
at `(A, -)`, whose naturality is its naturality at a morphism `(𝟙 A, g)`. -/
def derivedPullbackTensorIsoFixedSource :
    (derivedTensorProductFunctor Y.O).obj A ⋙ derivedPullback f ≅
      derivedPullback f ⋙
        (derivedTensorProductFunctor X.O).obj ((derivedPullback f).obj A) :=
  NatIso.ofComponents
    (fun N => (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso f hmos).app (A, N))
    (fun {N N'} g => by
      have h := (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso f hmos).hom.naturality
        (X := ((A, N) :
          DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ×
          DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))))
        (Y := ((A, N') :
          DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ×
          DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))))
        ((𝟙 A, g) : ((A, N) :
            DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ×
            DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) ⟶
          (A, N'))
      simpa using h)

/-! ### The two composite adjunctions -/

/-- The composite of the derived adjunction of Stacks 07A6 with the tensor–internal-hom
adjunction of Stacks 08J8 on the source topos:

`Lf^* ⋙ (Lf^*A ⊗^𝐋_{O'} -) ⊣ RSheafHom_{O'}(Lf^*A, -) ⋙ Rf_*`.

Its right adjoint is the left-hand side `M ↦ Rf_* RSheafHom_{O'}(Lf^*A, M)` of the formula of
this file. -/
def derivedPullbackTensorSheafHomAdjunction :
    derivedPullback f ⋙
        (derivedTensorProductFunctor X.O).obj ((derivedPullback f).obj A) ⊣
      (RingedSite.derivedSheafHomBifunctor (RingedTopos.toRingedSite X)).obj
          (op ((derivedPullback f).obj A)) ⋙ derivedPushforward f :=
  (derivedAdjunction f hmos).comp
    (RingedSite.interfaceDerivedTensorSheafHomAdjunction (RingedTopos.toRingedSite X)
      ((derivedPullback f).obj A))

/-- The composite of the tensor–internal-hom adjunction of Stacks 08J8 on the target topos with
the derived adjunction of Stacks 07A6:

`(A ⊗^𝐋_O -) ⋙ Lf^* ⊣ Rf_* ⋙ RSheafHom_O(A, -)`.

Its right adjoint is the right-hand side `M ↦ RSheafHom_O(A, Rf_*M)` of the formula of this
file. -/
def derivedTensorPullbackSheafHomAdjunction :
    (derivedTensorProductFunctor Y.O).obj A ⋙ derivedPullback f ⊣
      derivedPushforward f ⋙
        (RingedSite.derivedSheafHomBifunctor (RingedTopos.toRingedSite Y)).obj (op A) :=
  (RingedSite.interfaceDerivedTensorSheafHomAdjunction (RingedTopos.toRingedSite Y) A).comp
    (derivedAdjunction f hmos)

/-- `derivedTensorPullbackSheafHomAdjunction` transported along Stacks 07A4 so that it has the
same left adjoint as `derivedPullbackTensorSheafHomAdjunction`. -/
def derivedTensorPullbackSheafHomAdjunction' :
    derivedPullback f ⋙
        (derivedTensorProductFunctor X.O).obj ((derivedPullback f).obj A) ⊣
      derivedPushforward f ⋙
        (RingedSite.derivedSheafHomBifunctor (RingedTopos.toRingedSite Y)).obj (op A) :=
  Adjunction.ofNatIsoLeft (derivedTensorPullbackSheafHomAdjunction f hmos A)
    (derivedPullbackTensorIsoFixedSource f hmos A)

/-! ### The isomorphism -/

/-- **`Rf_* RSheafHom_{O'}(Lf^*A, M) ≅ RSheafHom_O(A, Rf_*M)`, naturally in `M`.**

For a morphism of ringed topoi `f : (Sh(C), O') ⟶ (Sh(D), O)` presented by a morphism of the
underlying sites and an **arbitrary** object `A` of `D(O)`, the isomorphism of functors
`D(O') ⟶ D(O)`

`RSheafHom_{O'}(Lf^*A, -) ⋙ Rf_* ≅ Rf_* ⋙ RSheafHom_O(A, -)`.

Both functors are right adjoint to `N ↦ Lf^*A ⊗^𝐋_{O'} Lf^*N`: the first by composing the
derived adjunction of Stacks 07A6 with the tensor–internal-hom adjunction of Stacks 08J8 on the
source topos, the second by composing them the other way round and transporting along the
monoidality of derived pullback, Stacks 07A4.  The isomorphism is the uniqueness of right
adjoints, so it is not an unconstrained morphism between the two functors. -/
def derivedPushforwardSheafHomIso :
    (RingedSite.derivedSheafHomBifunctor (RingedTopos.toRingedSite X)).obj
          (op ((derivedPullback f).obj A)) ⋙ derivedPushforward f ≅
      derivedPushforward f ⋙
        (RingedSite.derivedSheafHomBifunctor (RingedTopos.toRingedSite Y)).obj (op A) :=
  Adjunction.rightAdjointUniq (derivedPullbackTensorSheafHomAdjunction f hmos A)
    (derivedTensorPullbackSheafHomAdjunction' f hmos A)

/-- **`Rf_* RSheafHom_{O'}(Lf^*A, M) ≅ RSheafHom_O(A, Rf_*M)`** at an object `M` of `D(O')`,
the value of `derivedPushforwardSheafHomIso`. -/
def derivedPushforwardSheafHomObjIso
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (derivedPushforward f).obj
        (((RingedSite.derivedSheafHomBifunctor (RingedTopos.toRingedSite X)).obj
          (op ((derivedPullback f).obj A))).obj M) ≅
      ((RingedSite.derivedSheafHomBifunctor (RingedTopos.toRingedSite Y)).obj (op A)).obj
        ((derivedPushforward f).obj M) :=
  (derivedPushforwardSheafHomIso f hmos A).app M

/-- The naturality of the isomorphism in `M`, spelled out at objects. -/
theorem derivedPushforwardSheafHomObjIso_naturality
    {M M' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (g : M ⟶ M') :
    (derivedPushforward f).map
          (((RingedSite.derivedSheafHomBifunctor (RingedTopos.toRingedSite X)).obj
            (op ((derivedPullback f).obj A))).map g) ≫
        (derivedPushforwardSheafHomObjIso f hmos A M').hom =
      (derivedPushforwardSheafHomObjIso f hmos A M).hom ≫
        ((RingedSite.derivedSheafHomBifunctor (RingedTopos.toRingedSite Y)).obj (op A)).map
          ((derivedPushforward f).map g) :=
  (derivedPushforwardSheafHomIso f hmos A).hom.naturality g

/-- **The isomorphism is pinned by the two units.**  Composing the unit of the first adjunction
with it gives the unit of the second, which is what the uniqueness of right adjoints produces.
Since the unit of an adjunction determines a transformation out of its right adjoint, this
determines the isomorphism. -/
theorem unit_derivedPushforwardSheafHomIso :
    (derivedPullbackTensorSheafHomAdjunction f hmos A).unit ≫
        Functor.whiskerLeft _ (derivedPushforwardSheafHomIso f hmos A).hom =
      (derivedTensorPullbackSheafHomAdjunction' f hmos A).unit :=
  Adjunction.unit_rightAdjointUniq_hom _ _

/-- **The isomorphism is pinned by the two counits.**  Pushing it into the common left adjoint
and composing with the counit of the second adjunction gives the counit of the first. -/
theorem derivedPushforwardSheafHomIso_counit :
    Functor.whiskerRight (derivedPushforwardSheafHomIso f hmos A).hom _ ≫
        (derivedTensorPullbackSheafHomAdjunction' f hmos A).counit =
      (derivedPullbackTensorSheafHomAdjunction f hmos A).counit :=
  Adjunction.rightAdjointUniq_hom_counit _ _

end Stacks.Cohomology.DerivedInternalHomPushforward

/-! ## Stacks 08J8 as an adjunction with a parameter -/

namespace AlgebraicGeometry.RingedSite

variable (Z : RingedSite.{u, u, u})
  [HasSheafify Z.J AddCommGrpCat.{u}]
  [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} Z.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} Z.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Z.O)
      (ComplexShape.up ℤ)]

/-- **Naturality of the derived currying isomorphism of Stacks 08J9 in the middle variable
alone**: the three-variable square `derivedCurryIso_natural` with identities in the source and
the target.  It is the companion of `derivedCurryIso_natural_fst` and
`derivedCurryIso_natural_thd`. -/
theorem derivedCurryIso_natural_snd
    (A : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)))
    {B B' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))}
    (v : B' ⟶ B)
    (W : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))) :
    ((derivedSheafHomBifunctor Z).obj (op A)).map
          (((derivedSheafHomBifunctor Z).map v.op).app W) ≫
        (derivedCurryIso Z A B' W).hom =
      (derivedCurryIso Z A B W).hom ≫
        ((derivedSheafHomBifunctor Z).map
          (((Stacks.SheafOfModules.derivedTensorProductFunctor Z).obj A).map v).op).app W := by
  have h := derivedCurryIso_natural Z (𝟙 A) v (𝟙 W)
  simp only [op_id, CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp,
    Category.comp_id] at h
  exact h

/-- The derived currying isomorphism of Stacks 08J9 read on degree-zero global
hypercohomology is natural in the middle variable: the square `derivedCurryIso_natural_snd`
pushed through `H⁰(C, -)`, on elements. -/
theorem homologyGlobalSections_derivedCurryIso_naturality_snd
    (A : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)))
    {B B' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))}
    (v : B' ⟶ B)
    (W : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)))
    (x : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections Z).obj
        (((derivedSheafHomBifunctor Z).obj (op A)).obj
          (((derivedSheafHomBifunctor Z).obj (op B)).obj W))) : Type u)) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections Z).map (derivedCurryIso Z A B' W).hom)
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections Z).map
            (((derivedSheafHomBifunctor Z).obj (op A)).map
              (((derivedSheafHomBifunctor Z).map v.op).app W))) x) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections Z).map
          (((derivedSheafHomBifunctor Z).map
            (((Stacks.SheafOfModules.derivedTensorProductFunctor Z).obj A).map v).op).app W))
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections Z).map (derivedCurryIso Z A B W).hom) x) := by
  rw [homologyGlobalSections_map_comp_apply, derivedCurryIso_natural_snd,
    ← homologyGlobalSections_map_comp_apply]

/-- One half of the transport of `derivedCurryIso_natural_snd` to morphism groups: the
transpose of `GS x ≫ RSheafHom(v, W)` is `GS` of the class obtained by applying the derived
internal Hom of `v` and then the derived currying isomorphism.

It is the naturality of Stacks 08JA in the target variable followed by Stacks 08J9 read on
degree-zero global hypercohomology. -/
theorem derivedCurryHomEquiv_globalSections_homologyMap_snd
    (A : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)))
    {B B' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))}
    (v : B' ⟶ B)
    (W : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)))
    (x : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections Z).obj
        (((derivedSheafHomBifunctor Z).obj (op A)).obj
          (((derivedSheafHomBifunctor Z).obj (op B)).obj W))) : Type u)) :
    derivedCurryHomEquiv Z A B' W
        (derivedSheafHomGlobalSectionsEquiv Z A
            (((derivedSheafHomBifunctor Z).obj (op B)).obj W) x ≫
          ((derivedSheafHomBifunctor Z).map v.op).app W) =
      derivedSheafHomGlobalSectionsEquiv Z
        (((Stacks.SheafOfModules.derivedTensorProductFunctor Z).obj A).obj B') W
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections Z).map (derivedCurryIso Z A B' W).hom)
          ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
            ((derivedModuleGlobalSections Z).map
              (((derivedSheafHomBifunctor Z).obj (op A)).map
                (((derivedSheafHomBifunctor Z).map v.op).app W))) x)) := by
  rw [← derivedSheafHomGlobalSectionsEquiv_naturality_target_globalMap Z
      (((derivedSheafHomBifunctor Z).map v.op).app W) x,
    derivedCurryHomEquiv_globalSections_homologyMap, derivedHomGlobalMap_snd_eq]

/-- The other half: the naturality of Stacks 08JA in the source variable, with the induced map
written as the one the derived internal Hom gives rather than through
`derivedHomGlobalMap`. -/
theorem derivedSheafHomGlobalSectionsEquiv_homologyMap_fst
    {A A' W : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))}
    (u : A' ⟶ A)
    (z : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections Z).obj
        (((derivedSheafHomBifunctor Z).obj (op A)).obj W)) : Type u)) :
    derivedSheafHomGlobalSectionsEquiv Z A' W
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections Z).map
            (((derivedSheafHomBifunctor Z).map u.op).app W)) z) =
      u ≫ derivedSheafHomGlobalSectionsEquiv Z A W z := by
  rw [← derivedHomGlobalMap_fst_eq, derivedSheafHomGlobalSectionsEquiv_naturality_source]

/-- **Stacks 08J8 is natural in its middle object.**  For `v : B' ⟶ B` and
`h : A ⟶ RSheafHom(B, W)`, the morphism `A ⊗^𝐋_O B' ⟶ W` matched with
`h ≫ RSheafHom(v, W)` is `1 ⊗ v` followed by the morphism matched with `h`.

This is the clause of the functoriality of Stacks 08J8 that
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryTargetNaturality` leaves
out, and it is what makes the formula of this file natural in `A`.  The proof is the one the
source and target clauses take there: the object-level square `derivedCurryIso_natural_snd` of
Stacks 08J9 read on degree-zero global hypercohomology, transported at both ends by the
naturality of Stacks 08JA in its two variables. -/
theorem derivedCurryHomEquiv_naturality_snd
    {A B B' W : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))}
    (v : B' ⟶ B)
    (h : A ⟶ ((derivedSheafHomBifunctor Z).obj (op B)).obj W) :
    derivedCurryHomEquiv Z A B' W (h ≫ ((derivedSheafHomBifunctor Z).map v.op).app W) =
      ((Stacks.SheafOfModules.derivedTensorProductFunctor Z).obj A).map v ≫
        derivedCurryHomEquiv Z A B W h := by
  obtain ⟨x, rfl⟩ := (derivedSheafHomGlobalSectionsEquiv Z A
    (((derivedSheafHomBifunctor Z).obj (op B)).obj W)).surjective h
  rw [derivedCurryHomEquiv_globalSections_homologyMap_snd,
    homologyGlobalSections_derivedCurryIso_naturality_snd,
    derivedSheafHomGlobalSectionsEquiv_homologyMap_fst,
    derivedCurryHomEquiv_globalSections_homologyMap]

/-- `derivedCurryHomEquiv_naturality_snd` read through the inverse bijection: the transpose
of `(K ⊗ g) ≫ φ` is the transpose of `φ` followed by `RSheafHom(g, M)`. -/
theorem derivedCurryHomEquiv_symm_naturality_middle
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)))
    {L L' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))}
    (g : L' ⟶ L)
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)))
    (φ : ((Stacks.SheafOfModules.derivedTensorProductFunctor Z).obj K).obj L ⟶ M) :
    (derivedCurryHomEquiv Z K L' M).symm
        (((Stacks.SheafOfModules.derivedTensorProductFunctor Z).obj K).map g ≫ φ) =
      (derivedCurryHomEquiv Z K L M).symm φ ≫
        ((derivedSheafHomBifunctor Z).map g.op).app M := by
  apply (derivedCurryHomEquiv Z K L' M).injective
  rw [AddEquiv.apply_symm_apply, derivedCurryHomEquiv_naturality_snd,
    AddEquiv.apply_symm_apply]

/-- The hom-set bijection of the adjunction
`AlgebraicGeometry.RingedSite.derivedTensorSheafHomAdjunction` of Stacks 08J8 is the inverse of
the tensor-internal-hom bijection `derivedCurryHomEquiv`, which is how it is built. -/
theorem derivedTensorSheafHomAdjunction_homEquiv
    (B K M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)))
    (φ : ((Stacks.SheafOfModules.derivedTensorProductFunctor Z).obj K).obj B ⟶ M) :
    (derivedTensorSheafHomAdjunction Z B).homEquiv K M φ =
      (derivedCurryHomEquiv Z K B M).symm φ := by
  rw [derivedTensorSheafHomAdjunction, Adjunction.mkOfHomEquiv_homEquiv, Equiv.coe_fn_mk]

/-- **Stacks 08J8 as an adjunction with a parameter**, tensoring on the second slot: the family
`- ⊗^𝐋_O B ⊣ RSheafHom(B, -)` of `derivedTensorSheafHomAdjunction` is natural in `B`.

The naturality axiom is `derivedCurryHomEquiv_symm_naturality_middle`, i.e. the naturality of
Stacks 08J8 in its middle object.  It is what makes `RSheafHom(g, -)` the conjugate of
`- ⊗^𝐋_O g`, hence what makes the right-hand side of the formula of this file natural in `A`
rather than only defined at each `A` separately. -/
def derivedTensorSheafHomParametrizedAdjunctionFlip :
    (Stacks.SheafOfModules.derivedTensorProductFunctor Z).flip ⊣₂
      derivedSheafHomBifunctor Z :=
  ParametrizedAdjunction.mk' (fun B => derivedTensorSheafHomAdjunction Z B)
    (fun {B B'} g {K M} φ => by
      rw [derivedTensorSheafHomAdjunction_homEquiv, derivedTensorSheafHomAdjunction_homEquiv,
        Functor.flip_map_app, derivedCurryHomEquiv_symm_naturality_middle])

/-- **Stacks 08J8 as an adjunction with a parameter**, tensoring on the first slot and over
`Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor`, the derived tensor product the
projection formula and Stacks 07A4 of this development are stated over:
`A ⊗^𝐋_O - ⊣ RSheafHom(A, -)`, naturally in `A`.

This is `derivedTensorSheafHomParametrizedAdjunctionFlip` transported along the two
isomorphisms of bifunctors that `interfaceDerivedTensorSheafHomAdjunction` transports its
members along — the flip comparison `derivedTensorFlipNatIso` and the comparison
`Stacks.SheafOfModules.DerivedMonoidal.interfaceTensorCanonicalIso` of the site's two derived
tensor products. -/
@[sga "7 VIII 1.1" "more general"]
def derivedTensorSheafHomParametrizedAdjunction :
    Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.O ⊣₂
      derivedSheafHomBifunctor Z :=
  Stacks.Duality.parametrizedOfNatIsoLeft
    (Stacks.Duality.parametrizedOfNatIsoLeft
      (derivedTensorSheafHomParametrizedAdjunctionFlip Z) (derivedTensorFlipNatIso Z).symm)
    (Stacks.SheafOfModules.DerivedMonoidal.interfaceTensorCanonicalIso Z)

end AlgebraicGeometry.RingedSite

/-! ## The formula as an isomorphism of bifunctors -/

namespace Stacks.Cohomology.DerivedInternalHomPushforward

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]
  (f : RingedToposSiteHom X Y)
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))]
  (hmos : f.u.IsMorphismOfSites Y.J X.J)

/-- **Stacks 07A4 with its first tensor slot fixed, as an isomorphism of bifunctors.**  The
family `derivedPullbackTensorIsoFixedSource` is natural in the fixed object `A` as well, because
Stacks 07A4 is an isomorphism of bifunctors on `D(O) × D(O)`. -/
def derivedPullbackTensorNatIsoFixedSource :
    (derivedTensorProductFunctor Y.O) ⋙
        (Functor.whiskeringRight
          (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
          (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
          (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).obj
            (derivedPullback f) ≅
      (derivedPullback f ⋙ derivedTensorProductFunctor X.O) ⋙
        (Functor.whiskeringLeft
          (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
          (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
          (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).obj
            (derivedPullback f) :=
  NatIso.ofComponents (fun A => derivedPullbackTensorIsoFixedSource f hmos A)
    (fun {A A'} a => by
      ext N
      have h := (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso f hmos).hom.naturality
        (X := ((A, N) :
          DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ×
          DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))))
        (Y := ((A', N) :
          DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ×
          DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))))
        ((a, 𝟙 N) : ((A, N) :
            DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ×
            DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) ⟶
          (A', N))
      simpa [derivedPullbackTensorIsoFixedSource] using h)

/-- `derivedPullbackTensorSheafHomAdjunction` as an adjunction with a parameter: the derived
adjunction of Stacks 07A6 composed with Stacks 08J8 on the source topos, with the parameter
`A` of `D(O)` entering through `Lf^*A`. -/
def derivedPullbackTensorSheafHomParametrizedAdjunction :
    ((derivedPullback f ⋙ derivedTensorProductFunctor X.O) ⋙
        (Functor.whiskeringLeft
          (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
          (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
          (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).obj
            (derivedPullback f)) ⊣₂
      (((derivedPullback f).op ⋙
          RingedSite.derivedSheafHomBifunctor (RingedTopos.toRingedSite X)) ⋙
        (Functor.whiskeringRight
          (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
          (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
          (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))).obj
            (derivedPushforward f)) :=
  Stacks.Duality.parametrizedCompSource
    (Stacks.Duality.parametrizedCompParam
      (RingedSite.derivedTensorSheafHomParametrizedAdjunction (RingedTopos.toRingedSite X))
      (derivedPullback f))
    (derivedAdjunction f hmos)

/-- `derivedTensorPullbackSheafHomAdjunction` as an adjunction with a parameter: Stacks 08J8 on
the target topos composed with the derived adjunction of Stacks 07A6. -/
def derivedTensorPullbackSheafHomParametrizedAdjunction :
    (derivedTensorProductFunctor Y.O ⋙
        (Functor.whiskeringRight
          (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
          (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
          (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).obj
            (derivedPullback f)) ⊣₂
      (RingedSite.derivedSheafHomBifunctor (RingedTopos.toRingedSite Y) ⋙
        (Functor.whiskeringLeft
          (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
          (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
          (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))).obj
            (derivedPushforward f)) :=
  Stacks.Duality.parametrizedCompTarget
    (RingedSite.derivedTensorSheafHomParametrizedAdjunction (RingedTopos.toRingedSite Y))
    (derivedAdjunction f hmos)

/-- **`Rf_* RSheafHom_{O'}(Lf^*A, M) ≅ RSheafHom_O(A, Rf_*M)`, naturally in `A` and in `M`.**

The isomorphism of bifunctors `D(O)ᵒᵖ ⥤ D(O') ⥤ D(O)`

`(Lf^*)ᵒᵖ ⋙ RSheafHom_{O'} ⋙ (- ⋙ Rf_*) ≅ RSheafHom_O ⋙ (Rf_* ⋙ -)`,

whose value at `(op A, M)` is `Rf_* RSheafHom_{O'}(Lf^*A, M) ≅ RSheafHom_O(A, Rf_*M)`.

Both bifunctors are the right half of an adjunction with a parameter whose left half is
`(A, N) ↦ Lf^*A ⊗^𝐋_{O'} Lf^*N`, so they are isomorphic by
`Stacks.Duality.parametrizedRightAdjointUniq`.  The naturality in `A` is thereby
reduced to the naturality of Stacks 08J8 in its middle object, which is what
`AlgebraicGeometry.RingedSite.derivedTensorSheafHomParametrizedAdjunction` packages. -/
def derivedPushforwardSheafHomBifunctorIso :
    (((derivedPullback f).op ⋙
          RingedSite.derivedSheafHomBifunctor (RingedTopos.toRingedSite X)) ⋙
        (Functor.whiskeringRight
          (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
          (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
          (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))).obj
            (derivedPushforward f)) ≅
      (RingedSite.derivedSheafHomBifunctor (RingedTopos.toRingedSite Y) ⋙
        (Functor.whiskeringLeft
          (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
          (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
          (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))).obj
            (derivedPushforward f)) :=
  Stacks.Duality.parametrizedRightAdjointUniq
    (derivedPullbackTensorSheafHomParametrizedAdjunction f hmos)
    (Stacks.Duality.parametrizedOfNatIsoLeft
      (derivedTensorPullbackSheafHomParametrizedAdjunction f hmos)
      (derivedPullbackTensorNatIsoFixedSource f hmos))

/-- **The formula at a fixed `M`, as an isomorphism of functors of `A`.**  For an object `M` of
`D(O')`, the isomorphism of functors `D(O)ᵒᵖ ⥤ D(O)`

`A ↦ Rf_* RSheafHom_{O'}(Lf^*A, M)` ≅ `A ↦ RSheafHom_O(A, Rf_*M)`.

Composing it with `S.op` for a system `S : J ⥤ D(O)` gives the isomorphism of the two towers
`n ↦ Rf_* RSheafHom_{O'}(Lf^*S n, M)` and `n ↦ RSheafHom_O(S n, Rf_*M)`, which is the form in
which a derived-limit argument consumes the formula. -/
def derivedPushforwardSheafHomIsoOfObj
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (derivedPullback f).op ⋙
        (RingedSite.derivedSheafHomBifunctor (RingedTopos.toRingedSite X)).flip.obj M ⋙
          derivedPushforward f ≅
      (RingedSite.derivedSheafHomBifunctor (RingedTopos.toRingedSite Y)).flip.obj
        ((derivedPushforward f).obj M) :=
  NatIso.ofComponents
    (fun A => ((derivedPushforwardSheafHomBifunctorIso f hmos).app A).app M)
    (fun {_A _B} φ => NatTrans.congr_app
      ((derivedPushforwardSheafHomBifunctorIso f hmos).hom.naturality φ) M)

end Stacks.Cohomology.DerivedInternalHomPushforward

end
