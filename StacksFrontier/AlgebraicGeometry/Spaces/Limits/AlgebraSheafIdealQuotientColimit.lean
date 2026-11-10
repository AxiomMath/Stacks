module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AlgebraSheafColimits
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FiniteAlgebraSurjectiveSystem
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The colimit of a filtered system of quotients of an algebra sheaf by sheaves of ideals

Let `F` be an algebraic space over a scheme `S`, let `ℬ` be a sheaf of commutative
`𝒪_F`-algebras on its small étale site and let `p ↦ ℐ_p` be a family of sheaves of ideals of `ℬ`
growing along a filtered index.  The quotients `ℬ/ℐ_p` of
`StacksFrontier.AlgebraicGeometry.Spaces.Limits.AlgebraSheafIdealQuotient` form a diagram, and a
morphism `f : ℬ ⟶ 𝒜` killing every `ℐ_p` makes `𝒜` the vertex of a cocone over it.  **This file
decides when that cocone is colimiting**, and it does so without computing the sections of a
sheafification anywhere.

## Main results

* `Stacks.SheafifyColimit.nonempty_isColimit_sheafifyCocone_iff`: **the sheafification of a
  cocone of presheaves whose vertex is a sheaf is colimiting exactly when the comparison out of
  the presheaf colimit lies in `CategoryTheory.GrothendieckTopology.W`**, i.e. becomes an
  isomorphism under sheafification.  Pure site theory; no colimit of sheaves is assumed to
  exist.
* `Stacks.Sites.isColimit_iSupQuotientCocone`: **for a filtered family of sheaves of ideals the
  objectwise quotient by the supremum is the colimit of the objectwise quotients.**
* `Stacks.Sites.isLocallySurjective_iSupQuotientLift_iff` and
  `Stacks.Sites.isLocallyInjective_iSupQuotientLift_iff`: **the comparison
  `ℬ/⨆ ℐ ⟶ 𝒜` is locally surjective exactly when `f` is, and locally injective exactly when
  every section of `ℬ` killed by `f` locally lies in one member of the family.**
* `AlgebraicGeometry.Space.nonempty_isColimit_idealQuotientAlgCocone_iff` and
  `...iff_locally`: **the cocone of quotients of an algebra sheaf on an algebraic space is
  colimiting exactly when `f` is locally surjective and `ker f` is the sheaf-theoretic supremum
  of the `ℐ_p`.**  An equivalence, not a criterion.
* `AlgebraicGeometry.Space.nonempty_isColimit_idealQuotientQcohCocone_of_locally`: the same two
  conditions supply the colimit assertion for the cocone
  `AlgebraicGeometry.Space.idealQuotientQcohCocone` of *quasi-coherent* algebras, which is the
  shape Stacks 082A and Stacks 086Z state it in.
* `exists_directed_isFinite_isFinitePresentation_locallySurjective_of_elementaryData`, in the
  namespace `AlgebraicGeometry.Space`:
  **Stacks 086Z over an elementary carried input.**  The conclusion of
  `AlgebraicGeometry.Space.exists_directed_isFinite_isFinitePresentation_locallySurjective`, with
  that theorem's three non-elementary conjuncts — quasi-coherence of every quotient `ℬ/ℐ_j`,
  finite presentation of every quotient `ℬ/ℐ_j`, and the colimit property of the constructed
  cocone — *derived* rather than carried, from quasi-coherence and finite presentation of `ℬ`
  itself, quasi-coherence and chartwise finite generation of the `ℐ_j`, and the two local
  conditions above.  A formally weaker statement than the theorem it calls, deliberately; see the
  section documentation at it.

## Implementation notes

### Why this needs no cohomology

`AlgebraicGeometry.Space.AlgebraSheaf.idealQuotient` is the *sheafification* of the objectwise
quotient, so the sections of `ℬ/ℐ_p` over an affine étale chart are not `ℬ(U)/ℐ_p(U)`;
identifying them is a vanishing statement for `H¹(U, ℐ_p)`, which is Stacks 0942 and is what the
affine-chart criteria of `StacksFrontier.AlgebraicGeometry.Spaces.Limits.AlgebraSheafColimits` would
need in order to be *verified*.  The route below avoids that question entirely.

Sheafification is a left adjoint, so it carries a colimit cocone of presheaves to a colimit
cocone of sheaves.  The diagram of quotients *is* the sheafification of the diagram of objectwise
quotients — `AlgebraicGeometry.Space.idealQuotientDiagram_comp_forget` is `rfl` — and the cocone
of quotients is the sheafification of the cocone of objectwise lifts.  So the only thing left to
decide is whether the comparison out of the *presheaf* colimit becomes invertible after
sheafification, which by `CategoryTheory.GrothendieckTopology.W_iff_isLocallyBijective` is local
bijectivity of a morphism of presheaves: a condition on sections of `ℬ` and of `𝒜`, with no
sheafification in it.  The presheaf colimit is computed objectwise, and objectwise a filtered
colimit of quotient rings is the quotient by the supremum of the ideals — the one place where
filteredness is used, through `Stacks.QuasiCompactColimit.isColimitOfJointlySurjective`.

The algebra structure costs nothing:
`AlgebraicGeometry.Space.AlgebraSheaf.nonempty_isColimit_forget_iff` is an equivalence, forgetting
it both preserving and reflecting connected colimits, and a filtered category is connected.

### Where the equivalence stops

At the level of all algebra sheaves the result is an **iff**.  At the level of the quasi-coherent
algebras only the sufficient direction survives: `AlgebraicGeometry.Space.QuasicoherentAlgebra` is
a full subcategory, and a full subcategory inclusion reflects colimits but need not preserve
them, so a cocone which is colimiting among the quasi-coherent algebras need not be colimiting
among all algebra sheaves.  This is why the colimit hypothesis carried by Stacks 086Z in
`AlgebraicGeometry.Space.exists_directed_isFinite_isFinitePresentation_locallySurjective` is not
replaced by the two local conditions: that would make the hypothesis stronger and so the theorem
weaker.  What this file supplies is the means to *discharge* that hypothesis from elementary
local data about `f` and the family.

## References

* [Stacks Project, Tag 082A](https://stacks.math.columbia.edu/tag/082A)
* [Stacks Project, Tag 086Z](https://stacks.math.columbia.edu/tag/086Z)
* [Stacks Project, Tag 0942](https://stacks.math.columbia.edu/tag/0942)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v₁ u₁ v₂ u₂ w' w u

namespace Stacks.SheafifyColimit

/-! ### Sheafifying a presheaf cocone -/

variable {C : Type u₁} [Category.{v₁} C] {A : Type u₂} [Category.{v₂} A]
    {K : GrothendieckTopology C} [HasSheafify K A] {P : Type w} [Category.{w'} P]
    {Q : P ⥤ Cᵒᵖ ⥤ A} {T : Sheaf K A}

/-- **The sheaf cocone obtained from a presheaf cocone whose vertex is a sheaf**: at `p` the
factorization of the presheaf leg through the sheafification of `Q.obj p`. -/
def sheafifyCocone (κ : Q ⟶ (Functor.const P).obj T.obj) :
    Q ⋙ presheafToSheaf K A ⟶ (Functor.const P).obj T where
  app p := ⟨sheafifyLift K (κ.app p) T.property⟩
  naturality p q g := by
    have e : Q.map g ≫ κ.app q = κ.app p := (κ.naturality g).trans (Category.comp_id _)
    refine Sheaf.hom_ext ?_
    refine Eq.trans ?_ (Category.comp_id (sheafifyLift K (κ.app p) T.property)).symm
    change sheafifyMap K (Q.map g) ≫ sheafifyLift K (κ.app q) T.property =
      sheafifyLift K (κ.app p) T.property
    rw [sheafifyMap_sheafifyLift, e]

/-- The comparison `sheafify (colim Q) ⟶ T` attached to a presheaf cocone and the map out of a
colimit cocone it induces. -/
def comparisonHom (c : Cocone Q) (η : c.pt ⟶ T.obj) :
    (presheafToSheaf K A).obj c.pt ⟶ T :=
  (presheafToSheaf K A).map η ≫ (sheafificationIso T).inv

/-- `comparisonHom c η` is the sheafification of `η` followed by the inverse of the
sheafification isomorphism of `T`. -/
theorem comparisonHom_eq (c : Cocone Q) (η : c.pt ⟶ T.obj) :
    comparisonHom c η =
      (presheafToSheaf K A).map η ≫ (sheafificationIso T).inv :=
  rfl

/-- If `η` factors the presheaf cocone `κ` through `c`, then each leg of the sheafified cocone of
`c` followed by `comparisonHom c η` is the corresponding leg of `sheafifyCocone κ`. -/
theorem mapCocone_ι_comp_comparisonHom (κ : Q ⟶ (Functor.const P).obj T.obj) (c : Cocone Q)
    (η : c.pt ⟶ T.obj) (hη : ∀ p, c.ι.app p ≫ η = κ.app p) (p : P) :
    ((presheafToSheaf K A).mapCocone c).ι.app p ≫ comparisonHom c η =
      (sheafifyCocone κ).app p := by
  rw [comparisonHom_eq]
  have hι : ((presheafToSheaf K A).mapCocone c).ι.app p =
      (presheafToSheaf K A).map (c.ι.app p) := rfl
  rw [hι, ← Category.assoc, ← Functor.map_comp, hη, Iso.comp_inv_eq]
  refine Sheaf.hom_ext ?_
  change sheafifyMap K (κ.app p) =
    sheafifyLift K (κ.app p) T.property ≫ toSheafify K T.obj
  refine sheafify_hom_ext K _ _ ((presheafToSheaf K A).obj T.obj).property ?_
  rw [← toSheafify_naturality, ← Category.assoc, toSheafify_sheafifyLift]
  rfl

/-- **The sheafification of a presheaf cocone with sheaf vertex is colimiting exactly when the
comparison out of the presheaf colimit becomes an isomorphism under sheafification.**

The sheafification functor is a left adjoint, so it carries the presheaf colimit cocone to a
colimiting cocone of sheaves; the cocone in question is that one followed by the comparison, and
a cocone receiving a colimiting cocone is colimiting exactly when the comparison is invertible.
No colimit of sheaves is assumed to exist. -/
theorem nonempty_isColimit_sheafifyCocone_iff (κ : Q ⟶ (Functor.const P).obj T.obj)
    (c : Cocone Q) (hc : IsColimit c) (η : c.pt ⟶ T.obj)
    (hη : ∀ p, c.ι.app p ≫ η = κ.app p) :
    Nonempty (IsColimit (Cocone.mk T (sheafifyCocone κ))) ↔ K.W η := by
  have hL : IsColimit ((presheafToSheaf K A).mapCocone c) :=
    isColimitOfPreserves (presheafToSheaf K A) hc
  have hdesc : hL.desc (Cocone.mk T (sheafifyCocone κ)) = comparisonHom c η :=
    (hL.uniq (Cocone.mk T (sheafifyCocone κ)) (comparisonHom c η)
      (mapCocone_ι_comp_comparisonHom κ c η hη)).symm
  rw [K.W_iff]
  constructor
  · rintro ⟨hd⟩
    have hiso : IsIso (hL.desc (Cocone.mk T (sheafifyCocone κ))) := by
      refine ⟨hd.desc ((presheafToSheaf K A).mapCocone c),
        hL.hom_ext fun p => ?_, hd.hom_ext fun p => ?_⟩
      · rw [← Category.assoc, hL.fac, hd.fac, Category.comp_id]
      · rw [← Category.assoc, hd.fac, hL.fac, Category.comp_id]
    rw [hdesc, comparisonHom_eq] at hiso
    exact IsIso.of_isIso_comp_right _ (sheafificationIso T).inv
  · intro h
    have hiso : IsIso (hL.desc (Cocone.mk T (sheafifyCocone κ))) := by
      rw [hdesc, comparisonHom_eq]
      infer_instance
    exact ⟨hL.ofPointIso⟩

end Stacks.SheafifyColimit

namespace Stacks.Sites

/-! ### The quotient by the supremum of a family of sheaves of ideals -/

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] {O : Sheaf J CommRingCat.{u}}
    {P : Type w} [Category.{w'} P]

/-- The ideal of sections of the supremum of a family of sheaves of ideals over an object of the
site: the supremum of the ideals of sections. -/
def iSupSectionIdeal (ι : P → IdealSubsheaf O) (X : Cᵒᵖ) : Ideal (O.obj.obj X) :=
  ⨆ p, sectionIdeal (ι p) X

omit [Category.{w', w} P] [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The ideal of sections of each member of the family is contained in the ideal of sections of
the supremum. -/
theorem le_iSupSectionIdeal (ι : P → IdealSubsheaf O) (p : P) (X : Cᵒᵖ) :
    sectionIdeal (ι p) X ≤ iSupSectionIdeal ι X :=
  le_iSup (fun q => sectionIdeal (ι q) X) p

omit [Category.{w', w} P] [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- Restriction along a morphism of the site maps sections of the supremum to sections of the
supremum. -/
theorem map_mem_iSupSectionIdeal (ι : P → IdealSubsheaf O) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    {a : O.obj.obj X} (ha : a ∈ iSupSectionIdeal ι X) :
    O.obj.map f a ∈ iSupSectionIdeal ι Y := by
  have h : iSupSectionIdeal ι X ≤ Ideal.comap (O.obj.map f).hom (iSupSectionIdeal ι Y) :=
    iSup_le fun p _ hx =>
      le_iSupSectionIdeal ι p Y (map_mem_sectionIdeal (ι p) f hx)
  exact h ha

/-- **The objectwise quotient of a sheaf of commutative rings by the supremum of a family of
sheaves of ideals**, a presheaf of commutative rings. -/
def iSupQuotientPresheaf (ι : P → IdealSubsheaf O) : Cᵒᵖ ⥤ CommRingCat.{u} where
  obj X := CommRingCat.of (O.obj.obj X ⧸ iSupSectionIdeal ι X)
  map {X Y} f := CommRingCat.ofHom
    (Ideal.quotientMap (iSupSectionIdeal ι Y) (O.obj.map f).hom
      fun _ h => map_mem_iSupSectionIdeal ι f h)
  map_id X := by
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    ext a
    change Ideal.Quotient.mk (iSupSectionIdeal ι X) (O.obj.map (𝟙 X) a) =
      Ideal.Quotient.mk (iSupSectionIdeal ι X) a
    rw [O.obj.map_id]
    rfl
  map_comp {X Y Z} f g := by
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    ext a
    change Ideal.Quotient.mk (iSupSectionIdeal ι Z) (O.obj.map (f ≫ g) a) =
      Ideal.Quotient.mk (iSupSectionIdeal ι Z) (O.obj.map g (O.obj.map f a))
    rw [O.obj.map_comp]
    rfl

/-- The comparison `O/I_p ⟶ O/⨆ I` of the quotient by one member of the family with the quotient
by the supremum. -/
def quotientPresheafToISup (ι : P → IdealSubsheaf O) (p : P) :
    quotientPresheaf (ι p) ⟶ iSupQuotientPresheaf ι where
  app X := CommRingCat.ofHom (Ideal.Quotient.factor (le_iSupSectionIdeal ι p X))
  naturality {X Y} f := by
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    ext a
    rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The objectwise comparison attached to the identical inclusion of a sheaf of ideals is the
identity. -/
theorem quotientPresheafMapOfLE_refl (I : IdealSubsheaf O) (h : I ≤ I) :
    quotientPresheafMapOfLE h = 𝟙 (quotientPresheaf I) := by
  ext X : 2
  apply CommRingCat.hom_ext
  apply Ideal.Quotient.ringHom_ext
  ext a
  rfl

/-- **The diagram `p ↦ O/I_p` of objectwise quotients of a sheaf of commutative rings by a family
of sheaves of ideals growing along the index.** -/
def quotientPresheafFunctor (ι : P → IdealSubsheaf O)
    (hι : ∀ p q : P, (p ⟶ q) → ι p ≤ ι q) : P ⥤ Cᵒᵖ ⥤ CommRingCat.{u} where
  obj p := quotientPresheaf (ι p)
  map {p q} g := quotientPresheafMapOfLE (hι p q g)
  map_id p := quotientPresheafMapOfLE_refl (ι p) (hι p p (𝟙 p))
  map_comp {_ _ _} _ _ := (quotientPresheafMapOfLE_comp _ _).symm

/-- The cocone of the objectwise quotients over the quotient by the supremum. -/
def iSupQuotientCocone (ι : P → IdealSubsheaf O) (hι : ∀ p q : P, (p ⟶ q) → ι p ≤ ι q) :
    quotientPresheafFunctor ι hι ⟶ (Functor.const P).obj (iSupQuotientPresheaf ι) where
  app p := quotientPresheafToISup ι p
  naturality p q g := by
    ext X : 2
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    ext a
    rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- For a filtered family of sheaves of ideals growing along the index, the ideals of sections
over a fixed object form a directed family. -/
theorem directed_sectionIdeal (ι : P → IdealSubsheaf O) [IsFiltered P]
    (hι : ∀ p q : P, (p ⟶ q) → ι p ≤ ι q) (X : Cᵒᵖ) :
    Directed (· ≤ ·) fun p => sectionIdeal (ι p) X := by
  intro p q
  have hle : ∀ {p q : P}, (p ⟶ q) → sectionIdeal (ι p) X ≤ sectionIdeal (ι q) X :=
    fun g _ ha => SheafOfModules.Submodule.le_iff.1 (hι _ _ g) X ha
  exact ⟨IsFiltered.max p q, hle (IsFiltered.leftToMax p q), hle (IsFiltered.rightToMax p q)⟩

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- For a filtered family of sheaves of ideals growing along the index, a section lies in the
supremum exactly when it lies in some member of the family. -/
theorem mem_iSupSectionIdeal_iff (ι : P → IdealSubsheaf O) [IsFiltered P]
    (hι : ∀ p q : P, (p ⟶ q) → ι p ≤ ι q) (X : Cᵒᵖ) (a : O.obj.obj X) :
    a ∈ iSupSectionIdeal ι X ↔ ∃ p, a ∈ sectionIdeal (ι p) X :=
  have : Nonempty P := IsFiltered.nonempty
  Submodule.mem_iSup_of_directed _ (directed_sectionIdeal ι hι X)

/-- **For a filtered family of sheaves of ideals the objectwise quotient by the supremum is the
colimit of the objectwise quotients.**

Colimits of presheaves are detected on the sections over each object of the site, and over one
object this is the elementwise recognition of a filtered colimit of commutative rings: every
class modulo the supremum is a class modulo any one member, and two classes modulo `I_p` with the
same class modulo the supremum already agree modulo `I_r` for `r` beyond `p` and beyond an index
containing their difference. -/
@[ega "IV 5.13.1" "Clause (i), special case"]
def isColimit_iSupQuotientCocone (ι : P → IdealSubsheaf O) [IsFiltered P]
    (hι : ∀ p q : P, (p ⟶ q) → ι p ≤ ι q) :
    IsColimit (Cocone.mk (iSupQuotientPresheaf ι) (iSupQuotientCocone ι hι)) := by
  refine evaluationJointlyReflectsColimits _ fun X => ?_
  refine Stacks.QuasiCompactColimit.isColimitOfJointlySurjective _ ?_ ?_
  · intro x
    obtain ⟨p⟩ := IsFiltered.nonempty (C := P)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := iSupSectionIdeal ι X) x
    exact ⟨p, Ideal.Quotient.mk (sectionIdeal (ι p) X) a, rfl⟩
  · intro p x y hxy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := sectionIdeal (ι p) X) x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective (I := sectionIdeal (ι p) X) y
    have hab : a - b ∈ iSupSectionIdeal ι X := by
      have h : Ideal.Quotient.mk (iSupSectionIdeal ι X) a =
          Ideal.Quotient.mk (iSupSectionIdeal ι X) b := hxy
      exact (Submodule.Quotient.eq _).1 h
    obtain ⟨q, hq⟩ := (mem_iSupSectionIdeal_iff ι hι X _).1 hab
    refine ⟨IsFiltered.max p q, IsFiltered.leftToMax p q, ?_⟩
    have hle : sectionIdeal (ι q) X ≤ sectionIdeal (ι (IsFiltered.max p q)) X := fun _ ha =>
      SheafOfModules.Submodule.le_iff.1 (hι q _ (IsFiltered.rightToMax p q)) X ha
    exact (Submodule.Quotient.eq _).2 (hle hq)

/-- The factorization of a morphism of presheaves of commutative rings killing a sheaf of ideals
through the objectwise quotient by it. -/
def quotientPresheafLift (I : IdealSubsheaf O) {R : Cᵒᵖ ⥤ CommRingCat.{u}} (g : O.obj ⟶ R)
    (hI : ∀ (X : Cᵒᵖ) (a : O.obj.obj X), a ∈ I.obj X → (g.app X).hom a = 0) :
    quotientPresheaf I ⟶ R where
  app X := CommRingCat.ofHom
    (Ideal.Quotient.lift (sectionIdeal I X) (g.app X).hom fun a ha => hI X a ha)
  naturality {X Y} f := by
    apply CommRingCat.hom_ext
    refine RingHom.ext fun x => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ConcreteCategory.congr_hom (g.naturality f) a

omit [Category.{w', w} P] [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- A morphism killing every member of a family of sheaves of ideals kills the sections of their
supremum. -/
theorem apply_eq_zero_of_mem_iSupSectionIdeal (ι : P → IdealSubsheaf O)
    {R : Cᵒᵖ ⥤ CommRingCat.{u}} (g : O.obj ⟶ R)
    (hI : ∀ (p : P) (X : Cᵒᵖ) (a : O.obj.obj X), a ∈ (ι p).obj X → (g.app X).hom a = 0)
    (X : Cᵒᵖ) (a : O.obj.obj X) (ha : a ∈ iSupSectionIdeal ι X) : (g.app X).hom a = 0 := by
  have h : iSupSectionIdeal ι X ≤ RingHom.ker (g.app X).hom :=
    iSup_le fun p _ hx => RingHom.mem_ker.2 (hI p X _ hx)
  exact RingHom.mem_ker.1 (h ha)

/-- The factorization of a morphism of presheaves of commutative rings killing every member of a
family of sheaves of ideals through the objectwise quotient by their supremum. -/
def iSupQuotientLift (ι : P → IdealSubsheaf O) {R : Cᵒᵖ ⥤ CommRingCat.{u}} (g : O.obj ⟶ R)
    (hI : ∀ (p : P) (X : Cᵒᵖ) (a : O.obj.obj X), a ∈ (ι p).obj X → (g.app X).hom a = 0) :
    iSupQuotientPresheaf ι ⟶ R where
  app X := CommRingCat.ofHom
    (Ideal.Quotient.lift (iSupSectionIdeal ι X) (g.app X).hom
      (apply_eq_zero_of_mem_iSupSectionIdeal ι g hI X))
  naturality {X Y} f := by
    apply CommRingCat.hom_ext
    refine RingHom.ext fun x => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := iSupSectionIdeal ι X) x
    exact ConcreteCategory.congr_hom (g.naturality f) a

omit [Category.{w', w} P] [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- For `I ≤ I'`, the comparison `O/I ⟶ O/I'` followed by the factorization of `g` through `O/I'`
is the factorization of `g` through `O/I`. -/
theorem quotientPresheafMapOfLE_comp_quotientPresheafLift {I I' : IdealSubsheaf O} (h : I ≤ I')
    {R : Cᵒᵖ ⥤ CommRingCat.{u}} (g : O.obj ⟶ R)
    (hI : ∀ (X : Cᵒᵖ) (a : O.obj.obj X), a ∈ I.obj X → (g.app X).hom a = 0)
    (hI' : ∀ (X : Cᵒᵖ) (a : O.obj.obj X), a ∈ I'.obj X → (g.app X).hom a = 0) :
    quotientPresheafMapOfLE h ≫ quotientPresheafLift I' g hI' = quotientPresheafLift I g hI := by
  ext X : 2
  apply CommRingCat.hom_ext
  apply Ideal.Quotient.ringHom_ext
  ext a
  rfl

omit [Category.{w', w} P] [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The comparison `O/I_p ⟶ O/⨆ I` followed by the factorization of `g` through `O/⨆ I` is the
factorization of `g` through `O/I_p`. -/
theorem quotientPresheafToISup_comp_iSupQuotientLift (ι : P → IdealSubsheaf O)
    {R : Cᵒᵖ ⥤ CommRingCat.{u}} (g : O.obj ⟶ R)
    (hI : ∀ (p : P) (X : Cᵒᵖ) (a : O.obj.obj X), a ∈ (ι p).obj X → (g.app X).hom a = 0)
    (p : P) :
    quotientPresheafToISup ι p ≫ iSupQuotientLift ι g hI =
      quotientPresheafLift (ι p) g (hI p) := by
  ext X : 2
  apply CommRingCat.hom_ext
  apply Ideal.Quotient.ringHom_ext
  ext a
  change ((iSupQuotientLift ι g hI).app X).hom
      ((Ideal.Quotient.factor (le_iSupSectionIdeal ι p X))
        (Ideal.Quotient.mk (sectionIdeal (ι p) X) a)) = (g.app X).hom a
  rw [Ideal.Quotient.factor_mk]
  rfl

/-! ### The two local conditions on the comparison -/

variable {R : Cᵒᵖ ⥤ CommRingCat.{u}}

omit [Category.{w', w} P] [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The factorization of `g` through `O/⨆ I` sends the class of a section `a` to `g a`. -/
theorem iSupQuotientLift_app_mk (ι : P → IdealSubsheaf O) (g : O.obj ⟶ R)
    (hI : ∀ (p : P) (X : Cᵒᵖ) (a : O.obj.obj X), a ∈ (ι p).obj X → (g.app X).hom a = 0)
    (X : Cᵒᵖ) (a : O.obj.obj X) :
    ((iSupQuotientLift ι g hI).app X).hom (Ideal.Quotient.mk (iSupSectionIdeal ι X) a) =
      (g.app X).hom a :=
  rfl

omit [Category.{w', w} P] [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The sieve of sections of `O/⨆ I` locally in the image of the comparison is the sieve of
sections locally in the image of the morphism it factors.**  The objectwise quotient map is
surjective, so a local preimage in the quotient is the class of a local preimage in `O`. -/
theorem imageSieve_iSupQuotientLift (ι : P → IdealSubsheaf O) (g : O.obj ⟶ R)
    (hI : ∀ (p : P) (X : Cᵒᵖ) (a : O.obj.obj X), a ∈ (ι p).obj X → (g.app X).hom a = 0)
    {X : C} (s : R.obj (op X)) :
    Presheaf.imageSieve (iSupQuotientLift ι g hI) s = Presheaf.imageSieve g s := by
  ext V i
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := iSupSectionIdeal ι (op V)) t
    exact ⟨a, (iSupQuotientLift_app_mk ι g hI (op V) a).symm.trans ht⟩
  · rintro ⟨a, ha⟩
    exact ⟨Ideal.Quotient.mk (iSupSectionIdeal ι (op V)) a,
      (iSupQuotientLift_app_mk ι g hI (op V) a).trans ha⟩

omit [Category.{w', w} P] [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The comparison is locally surjective exactly when the morphism it factors is.** -/
theorem isLocallySurjective_iSupQuotientLift_iff (ι : P → IdealSubsheaf O) (g : O.obj ⟶ R)
    (hI : ∀ (p : P) (X : Cᵒᵖ) (a : O.obj.obj X), a ∈ (ι p).obj X → (g.app X).hom a = 0) :
    Presheaf.IsLocallySurjective J (iSupQuotientLift ι g hI) ↔
      Presheaf.IsLocallySurjective J g := by
  refine ⟨fun _ => ⟨fun s => ?_⟩, fun _ => ⟨fun s => ?_⟩⟩
  · rw [← imageSieve_iSupQuotientLift ι g hI s]
    exact Presheaf.imageSieve_mem J _ s
  · rw [imageSieve_iSupQuotientLift ι g hI s]
    exact Presheaf.imageSieve_mem J _ s

/-- **The sieve of restrictions of a section of `O` lying in some member of a family of sheaves
of ideals.** -/
def memSieve (ι : P → IdealSubsheaf O) {X : Cᵒᵖ} (a : O.obj.obj X) : Sieve X.unop where
  arrows V h := ∃ p, O.obj.map h.op a ∈ sectionIdeal (ι p) (op V)
  downward_closed := by
    rintro V W h ⟨p, hp⟩ k
    refine ⟨p, ?_⟩
    have : O.obj.map (k ≫ h).op a = O.obj.map k.op (O.obj.map h.op a) := by
      rw [op_comp, O.obj.map_comp]
      rfl
    rw [this]
    exact map_mem_sectionIdeal (ι p) k.op hp

omit [Category.{w', w} P] [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- A morphism `h : V ⟶ X` lies in `memSieve ι a` exactly when the restriction of `a` along `h`
lies in the ideal of sections of some member of the family. -/
theorem mem_memSieve_iff (ι : P → IdealSubsheaf O) {X : Cᵒᵖ} (a : O.obj.obj X) {V : C}
    (h : V ⟶ X.unop) :
    memSieve ι a h ↔ ∃ p, O.obj.map h.op a ∈ sectionIdeal (ι p) (op V) :=
  Iff.rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The equalizer sieve of two classes in the quotient by the supremum is the sieve of
restrictions of the difference of representatives lying in some member of the family. -/
theorem equalizerSieve_mk_eq_memSieve (ι : P → IdealSubsheaf O) [IsFiltered P]
    (hι : ∀ p q : P, (p ⟶ q) → ι p ≤ ι q) {X : Cᵒᵖ} (a b : O.obj.obj X) :
    Presheaf.equalizerSieve (F := iSupQuotientPresheaf ι)
        (Ideal.Quotient.mk (iSupSectionIdeal ι X) a)
        (Ideal.Quotient.mk (iSupSectionIdeal ι X) b) =
      memSieve ι (a - b) := by
  ext V h
  have hmap : ∀ c : O.obj.obj X, (iSupQuotientPresheaf ι).map h.op
      (Ideal.Quotient.mk (iSupSectionIdeal ι X) c) =
      Ideal.Quotient.mk (iSupSectionIdeal ι (op V)) (O.obj.map h.op c) := fun _ => rfl
  change (iSupQuotientPresheaf ι).map h.op (Ideal.Quotient.mk (iSupSectionIdeal ι X) a) =
      (iSupQuotientPresheaf ι).map h.op (Ideal.Quotient.mk (iSupSectionIdeal ι X) b) ↔
    ∃ p, O.obj.map h.op (a - b) ∈ sectionIdeal (ι p) (op V)
  rw [hmap, hmap, map_sub]
  exact ⟨fun hab => (mem_iSupSectionIdeal_iff ι hι _ _).1 ((Submodule.Quotient.eq _).1 hab),
    fun hab => (Submodule.Quotient.eq _).2 ((mem_iSupSectionIdeal_iff ι hι _ _).2 hab)⟩

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The comparison is locally injective exactly when every section of `O` killed by the
morphism it factors locally lies in some member of the family.**

This is the elementary form of the colimit condition: no section of a sheafification appears in
it, only sections of `O` and membership in the members of the family. -/
theorem isLocallyInjective_iSupQuotientLift_iff (ι : P → IdealSubsheaf O) [IsFiltered P]
    (hι : ∀ p q : P, (p ⟶ q) → ι p ≤ ι q) (g : O.obj ⟶ R)
    (hI : ∀ (p : P) (X : Cᵒᵖ) (a : O.obj.obj X), a ∈ (ι p).obj X → (g.app X).hom a = 0) :
    Presheaf.IsLocallyInjective J (iSupQuotientLift ι g hI) ↔
      ∀ (X : Cᵒᵖ) (a : O.obj.obj X), (g.app X).hom a = 0 → memSieve ι a ∈ J X.unop := by
  constructor
  · intro h X a ha
    have hz : ((iSupQuotientLift ι g hI).app X).hom
          (Ideal.Quotient.mk (iSupSectionIdeal ι X) a) =
        ((iSupQuotientLift ι g hI).app X).hom
          (Ideal.Quotient.mk (iSupSectionIdeal ι X) 0) := by
      rw [iSupQuotientLift_app_mk, iSupQuotientLift_app_mk, ha, map_zero]
    have := Presheaf.equalizerSieve_mem J (iSupQuotientLift ι g hI) _ _ hz
    rwa [equalizerSieve_mk_eq_memSieve ι hι, sub_zero] at this
  · intro h
    refine ⟨fun {X} x y hxy => ?_⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := iSupSectionIdeal ι X) x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective (I := iSupSectionIdeal ι X) y
    rw [equalizerSieve_mk_eq_memSieve ι hι]
    refine h X (a - b) ?_
    rw [map_sub, ← iSupQuotientLift_app_mk ι g hI X a, ← iSupQuotientLift_app_mk ι g hI X b, hxy,
      sub_self]

end Stacks.Sites

namespace AlgebraicGeometry.Space

/-! ### The colimit of the system of quotients of an algebra sheaf on an algebraic space -/

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {Y : AlgebraicSpaces B S hS}

/-- **The diagram `p ↦ ℬ(·)/ℐ_p(·)` of objectwise quotients** underlying the diagram
`AlgebraicGeometry.Space.idealQuotientDiagram` of quotients of `ℬ` by the family. -/
abbrev idealQuotientPresheafDiagram (ℬ : AlgebraSheaf.{u, u} B S hS Y.1 Y.2) {P : Type u}
    [SmallCategory P] (ι : P → ℬ.IdealSheaf) (hι : ∀ p q : P, (p ⟶ q) → ι p ≤ ι q) :
    P ⥤ (SmallEtale B S hS Y.1)ᵒᵖ ⥤ CommRingCat.{u} :=
  Stacks.Sites.quotientPresheafFunctor (O := ℬ.right) ι hι

/-- **The diagram of quotients is the sheafification of the diagram of objectwise quotients**:
the quotient of an algebra sheaf by a sheaf of ideals is by construction the sheafification of
the objectwise quotient, and its comparisons are the sheafifications of the objectwise ones. -/
theorem idealQuotientDiagram_comp_forget (ℬ : AlgebraSheaf.{u, u} B S hS Y.1 Y.2) {P : Type u}
    [SmallCategory P] (ι : P → ℬ.IdealSheaf) (hι : ∀ p q : P, (p ⟶ q) → ι p ≤ ι q) :
    idealQuotientDiagram ℬ ι hι ⋙ AlgebraSheaf.forget =
      idealQuotientPresheafDiagram ℬ ι hι ⋙
        presheafToSheaf (SmallEtale.topology B S hS Y.1) CommRingCat.{u} :=
  rfl

/-- The cocone of the objectwise quotients over the underlying presheaf of the target. -/
def idealQuotientPresheafCocone (ℬ : AlgebraSheaf.{u, u} B S hS Y.1 Y.2) {P : Type u}
    [SmallCategory P] (ι : P → ℬ.IdealSheaf) (hι : ∀ p q : P, (p ⟶ q) → ι p ≤ ι q)
    (A : AlgebraSheaf.{u, u} B S hS Y.1 Y.2) (f : ℬ ⟶ A)
    (hkill : ∀ (p : P) (U : (SmallEtale B S hS Y.1)ᵒᵖ) (a : ℬ.right.obj.obj U),
      a ∈ (ι p).obj U → (f.right.hom.app U).hom a = 0) :
    idealQuotientPresheafDiagram ℬ ι hι ⟶ (Functor.const P).obj A.right.obj where
  app p := Stacks.Sites.quotientPresheafLift (O := ℬ.right) (ι p) f.right.hom (hkill p)
  naturality p q g :=
    (Stacks.Sites.quotientPresheafMapOfLE_comp_quotientPresheafLift (O := ℬ.right)
      (hι p q g) f.right.hom (hkill p) (hkill q)).trans (Category.comp_id _).symm

/-- **The cocone of the system of quotients over the target, at the level of algebra sheaves.**
Its leg at `p` is the factorization of `f` through `ℬ ⟶ ℬ/ℐ_p`; this is the algebra-sheaf
version of `AlgebraicGeometry.Space.idealQuotientQcohCocone`. -/
def idealQuotientAlgCocone (ℬ : AlgebraSheaf.{u, u} B S hS Y.1 Y.2) {P : Type u}
    [SmallCategory P] (ι : P → ℬ.IdealSheaf) (hι : ∀ p q : P, (p ⟶ q) → ι p ≤ ι q)
    (A : AlgebraSheaf.{u, u} B S hS Y.1 Y.2) (f : ℬ ⟶ A)
    (hkill : ∀ (p : P) (U : (SmallEtale B S hS Y.1)ᵒᵖ) (a : ℬ.right.obj.obj U),
      a ∈ (ι p).obj U → (f.right.hom.app U).hom a = 0) :
    idealQuotientDiagram ℬ ι hι ⟶ (Functor.const P).obj A where
  app p := AlgebraSheaf.idealQuotientLift f (ι p) (hkill p)
  naturality p q g :=
    (AlgebraSheaf.idealQuotientMapOfLE_comp_idealQuotientLift f (hι p q g)
      (hkill p) (hkill q)).trans (Category.comp_id _).symm

/-- Forgetting the algebra structure takes the cocone of quotients to the sheafification of the
cocone of objectwise quotients. -/
theorem forget_mapCocone_idealQuotientAlgCocone (ℬ : AlgebraSheaf.{u, u} B S hS Y.1 Y.2)
    {P : Type u} [SmallCategory P] (ι : P → ℬ.IdealSheaf)
    (hι : ∀ p q : P, (p ⟶ q) → ι p ≤ ι q) (A : AlgebraSheaf.{u, u} B S hS Y.1 Y.2) (f : ℬ ⟶ A)
    (hkill : ∀ (p : P) (U : (SmallEtale B S hS Y.1)ᵒᵖ) (a : ℬ.right.obj.obj U),
      a ∈ (ι p).obj U → (f.right.hom.app U).hom a = 0) :
    AlgebraSheaf.forget.mapCocone (Cocone.mk A (idealQuotientAlgCocone ℬ ι hι A f hkill)) =
      Cocone.mk A.right
        (Stacks.SheafifyColimit.sheafifyCocone (idealQuotientPresheafCocone ℬ ι hι A f hkill)) :=
  rfl

/-- **The constructed cocone of quotients of an algebra sheaf is colimiting exactly when the
comparison `ℬ/⨆ ℐ ⟶ 𝒜` out of the objectwise quotient by the supremum of the family becomes an
isomorphism under sheafification.**

Both halves are genuine: forgetting the algebra structure reflects *and* preserves connected
colimits, so nothing is lost in passing to sheaves of rings, and the sheafification of the
objectwise colimit is the colimit of the sheafifications because sheafification is a left
adjoint.  The objectwise colimit of the quotients is the quotient by the supremum, the family
being filtered. -/
theorem nonempty_isColimit_idealQuotientAlgCocone_iff
    (ℬ : AlgebraSheaf.{u, u} B S hS Y.1 Y.2) {P : Type u} [SmallCategory P] [IsFiltered P]
    (ι : P → ℬ.IdealSheaf) (hι : ∀ p q : P, (p ⟶ q) → ι p ≤ ι q)
    (A : AlgebraSheaf.{u, u} B S hS Y.1 Y.2) (f : ℬ ⟶ A)
    (hkill : ∀ (p : P) (U : (SmallEtale B S hS Y.1)ᵒᵖ) (a : ℬ.right.obj.obj U),
      a ∈ (ι p).obj U → (f.right.hom.app U).hom a = 0) :
    Nonempty (IsColimit (Cocone.mk A (idealQuotientAlgCocone ℬ ι hι A f hkill))) ↔
      (SmallEtale.topology B S hS Y.1).W
        (Stacks.Sites.iSupQuotientLift (O := ℬ.right) ι f.right.hom hkill) := by
  have : IsConnected P := IsFiltered.isConnected P
  rw [AlgebraSheaf.nonempty_isColimit_forget_iff,
    forget_mapCocone_idealQuotientAlgCocone ℬ ι hι A f hkill]
  have hfac : ∀ p : P, Stacks.Sites.quotientPresheafToISup (O := ℬ.right) ι p ≫
        Stacks.Sites.iSupQuotientLift (O := ℬ.right) ι f.right.hom hkill =
      (idealQuotientPresheafCocone ℬ ι hι A f hkill).app p := fun p =>
    Stacks.Sites.quotientPresheafToISup_comp_iSupQuotientLift (O := ℬ.right) ι f.right.hom
      hkill p
  exact Stacks.SheafifyColimit.nonempty_isColimit_sheafifyCocone_iff
    (idealQuotientPresheafCocone ℬ ι hι A f hkill) _
    (Stacks.Sites.isColimit_iSupQuotientCocone (O := ℬ.right) ι hι) _ hfac

/-- **The elementary form of the colimit condition.**  The constructed cocone of quotients is
colimiting exactly when `f` is locally surjective and every section of `ℬ` killed by `f` locally
lies in one member of the family — that is, exactly when `f` is locally surjective with
`ker f` the sheaf-theoretic supremum of the `ℐ_p`.

Neither condition mentions the sections of a sheafification: both are statements about the
sections of `ℬ` and of `𝒜` over the objects of the small étale site and about membership in the
members of the family. -/
theorem nonempty_isColimit_idealQuotientAlgCocone_iff_locally
    (ℬ : AlgebraSheaf.{u, u} B S hS Y.1 Y.2) {P : Type u} [SmallCategory P] [IsFiltered P]
    (ι : P → ℬ.IdealSheaf) (hι : ∀ p q : P, (p ⟶ q) → ι p ≤ ι q)
    (A : AlgebraSheaf.{u, u} B S hS Y.1 Y.2) (f : ℬ ⟶ A)
    (hkill : ∀ (p : P) (U : (SmallEtale B S hS Y.1)ᵒᵖ) (a : ℬ.right.obj.obj U),
      a ∈ (ι p).obj U → (f.right.hom.app U).hom a = 0) :
    Nonempty (IsColimit (Cocone.mk A (idealQuotientAlgCocone ℬ ι hι A f hkill))) ↔
      (Presheaf.IsLocallySurjective (SmallEtale.topology B S hS Y.1) f.right.hom ∧
        ∀ (U : (SmallEtale B S hS Y.1)ᵒᵖ) (a : ℬ.right.obj.obj U),
          (f.right.hom.app U).hom a = 0 →
            Stacks.Sites.memSieve (O := ℬ.right) ι a ∈ SmallEtale.topology B S hS Y.1 U.unop) := by
  rw [nonempty_isColimit_idealQuotientAlgCocone_iff ℬ ι hι A f hkill,
    GrothendieckTopology.W_iff_isLocallyBijective,
    Stacks.Sites.isLocallyInjective_iSupQuotientLift_iff (O := ℬ.right) ι hι f.right.hom hkill,
    Stacks.Sites.isLocallySurjective_iSupQuotientLift_iff (O := ℬ.right) ι f.right.hom hkill]
  exact and_comm

/-- **The colimit assertion of Stacks 082A and Stacks 086Z, from the two local conditions.**
A cocone of *quasi-coherent* algebras is colimiting as soon as its image in all algebra sheaves
is, the inclusion being fully faithful; so the elementary conditions of
`AlgebraicGeometry.Space.nonempty_isColimit_idealQuotientAlgCocone_iff_locally` suffice for the
cocone `AlgebraicGeometry.Space.idealQuotientQcohCocone`.

Only this direction holds at the quasi-coherent level: a full subcategory inclusion reflects
colimits but need not preserve them, so a colimit computed among the quasi-coherent algebras
need not be one among all algebra sheaves. -/
theorem nonempty_isColimit_idealQuotientQcohCocone_of_locally
    (ℬ : AlgebraSheaf.{u, u} B S hS Y.1 Y.2) {P : Type u} [SmallCategory P] [IsFiltered P]
    (ι : P → ℬ.IdealSheaf) (hι : ∀ p q : P, (p ⟶ q) → ι p ≤ ι q)
    (A : QuasicoherentAlgebra B S hS Y) (f : ℬ ⟶ A.obj)
    (hkill : ∀ (p : P) (U : (SmallEtale B S hS Y.1)ᵒᵖ) (a : ℬ.right.obj.obj U),
      a ∈ (ι p).obj U → (f.right.hom.app U).hom a = 0)
    (hqcoh : ∀ p, (ℬ.idealQuotient (ι p)).IsQuasicoherent)
    (hsurj : Presheaf.IsLocallySurjective (SmallEtale.topology B S hS Y.1) f.right.hom)
    (hmem : ∀ (U : (SmallEtale B S hS Y.1)ᵒᵖ) (a : ℬ.right.obj.obj U),
      (f.right.hom.app U).hom a = 0 →
        Stacks.Sites.memSieve (O := ℬ.right) ι a ∈ SmallEtale.topology B S hS Y.1 U.unop) :
    Nonempty (IsColimit (Cocone.mk A (idealQuotientQcohCocone ℬ ι hι A f hkill hqcoh))) := by
  obtain ⟨hc⟩ := (nonempty_isColimit_idealQuotientAlgCocone_iff_locally ℬ ι hι A.obj f
    hkill).2 ⟨hsurj, hmem⟩
  exact ⟨isColimit_of_isColimit_quasicoherentAlgebraInclusion _ hc⟩

/-! ### Stacks 086Z over elementary data

The carried input `hsource` of
`AlgebraicGeometry.Space.exists_directed_isFinite_isFinitePresentation_locallySurjective` asks,
of the family of sheaves of ideals it produces, for three things that are not statements about
sections of `ℬ` and of `𝒜`: quasi-coherence of every quotient `ℬ/ℐ_j`, finite presentation of
every quotient `ℬ/ℐ_j`, and the colimit property of the constructed cocone of quotients.  The
theorem below asks for none of the three.  In their place it asks for quasi-coherence and finite
presentation of `ℬ` *itself*, quasi-coherence of each `ℐ_j` as an `𝒪_Y`-module together with
finite generation of its ideal of sections over each affine étale chart, and the two local
conditions of
`AlgebraicGeometry.Space.nonempty_isColimit_idealQuotientAlgCocone_iff_locally` — and it derives
the three conjuncts it drops, by
`AlgebraicGeometry.Space.AlgebraSheaf.isQuasicoherent_idealQuotient`,
`AlgebraicGeometry.Space.AlgebraSheaf.isFinitePresentation_idealQuotient` and
`AlgebraicGeometry.Space.nonempty_isColimit_idealQuotientQcohCocone_of_locally`.

This is *not* a strengthening of that theorem and does not replace it.  None of the four
hypotheses it adds follows from the conjuncts it removes, so its carried input is strictly
stronger and it is, as a statement, strictly weaker; the original is left exactly as it stands
and keeps the unrestricted reading of the tag.  What it is for is that its carried input is
elementary: every conjunct of it is a condition on the sections of `ℬ`, of the `ℐ_j` and of `𝒜`
over the objects of the small étale site, or on one affine étale chart, with no sheafification
and no colimit in any of them.  It is therefore the form of Stacks 086Z that the source's own
construction can be fed into once quasi-coherence and finite presentation of
`AlgebraicGeometry.Space.symmetricAlgebraSheaf` become available at this level; those two, and
integrality at one index, are what remain. -/

/-- **Stacks Project, Tag 086Z, over elementary data about `ℬ` and the family of ideals.**  Same
conclusion as
`AlgebraicGeometry.Space.exists_directed_isFinite_isFinitePresentation_locallySurjective`: `A` is
the colimit of a system of quasi-coherent `𝒪_Y`-algebras over a nonempty directed preorder, every
member finite and of finite presentation and every transition map locally surjective.

The carried input no longer mentions the quotients `ℬ/ℐ_j` except at the single index where
integrality is asked.  It asks instead: `ℬ` quasi-coherent and of finite presentation, each `ℐ_j`
quasi-coherent as an `𝒪_Y`-module with finitely generated ideal of sections over each affine
étale chart, `f` locally surjective, and every section of `ℬ` which `f` kills locally a section
of some `ℐ_j`.  Those are the data of the first three steps of the source's proof and nothing
more.

See the section documentation above: this is a formally weaker statement than the theorem it
calls, deliberately, and it does not make Stacks 086Z unconditional. -/
@[stacks 086Z "the same conclusion as \
AlgebraicGeometry.Space.exists_directed_isFinite_isFinitePresentation_locallySurjective — the \
directedness of the index, the finiteness and the finite presentation of every stage, the \
surjectivity of every transition map and the colimit — but over an ELEMENTARY carried input in \
place of that theorem's hsource. THIS REGISTRATION IS FORMALLY WEAKER THAN THAT ONE AND DOES NOT \
REPLACE IT: the carried input here is strictly stronger, so the unrestricted reading of the tag \
remains the one carried there. What this registration claims is that the three non-elementary \
conjuncts of hsource — quasi-coherence of every quotient B/I_j, finite presentation of every \
quotient B/I_j, and the colimit property of the constructed cocone — are each DERIVABLE, and it \
derives them: quasi-coherence from quasi-coherence of B and of I_j by \
AlgebraicGeometry.Space.AlgebraSheaf.isQuasicoherent_idealQuotient, finite presentation from \
finite presentation of B and finite generation of the ideal of sections I_j(W) over each affine \
etale chart by AlgebraicGeometry.Space.AlgebraSheaf.isFinitePresentation_idealQuotient, and the \
colimit from local surjectivity of f together with local membership in the family of every \
section f kills by \
AlgebraicGeometry.Space.nonempty_isColimit_idealQuotientQcohCocone_of_locally. Every conjunct \
that remains carried is a condition on sections of B, of the I_j and of A over the objects of \
the small etale site, or on a single affine etale chart. STILL CARRIED, and NOT dischargeable in \
this tree today: (i) quasi-coherence of AlgebraicGeometry.Space.symmetricAlgebraSheaf for a \
quasi-coherent module, which is the B of the source and is recorded as absent in \
StacksFrontier.AlgebraicGeometry.Spaces.SymmetricAlgebraSheafMap (Stacks 01CK/01CL hold for a \
ringed space, as \
Stacks.SheafOfModules.isQuasicoherent_symmetricAlgebraSheaf_of_isQuasicoherent, but not for the \
small etale site of an algebraic space); (ii) finite presentation of that same Sym(F), the \
sections of which over a chart are only LOCALLY finite sums of homogeneous ones; (iii) \
integrality at one index, the fourth step of the source. Note also that Stacks 086Y, \
AlgebraicGeometry.Space.exists_directed_isFinitePresentation_epi_of_isFiniteType, is itself \
proved only over three carried inputs h07V9, hstage and hcoker, so Stacks 086Z is NOT \
unconditional in this tree by this route or any other presently available"]
theorem exists_directed_isFinite_isFinitePresentation_locallySurjective_of_elementaryData
    (A : QuasicoherentAlgebra B S hS Y)
    (hqc : IsQuasiCompactSpace B S hS Y.obj)
    (hqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y.obj)
    (hA : A.obj.IsFinite)
    (hdata :
      IsQuasiCompactSpace B S hS Y.obj →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y.obj →
      A.obj.IsFinite →
        ∃ (ℬ : AlgebraSheaf.{u, u} B S hS Y.1 Y.2) (f : ℬ ⟶ A.obj) (J : Type u)
          (inst : SmallCategory J),
          let _ := inst
          ∃ (_ : IsFiltered J) (ι : J → ℬ.IdealSheaf)
            (_ : ∀ j j' : J, (j ⟶ j') → ι j ≤ ι j'),
            (∀ (j : J) (U : (SmallEtale B S hS Y.1)ᵒᵖ) (a : ℬ.right.obj.obj U),
                a ∈ (ι j).obj U → (f.right.hom.app U).hom a = 0) ∧
              ℬ.IsQuasicoherent ∧ ℬ.IsFinitePresentation ∧
              (∀ j, (AlgebraSheaf.idealModule ℬ (ι j)).IsQuasicoherentOnSite) ∧
              (∀ (j : J) (W : SmallEtale B S hS Y.1),
                IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj W) →
                  (Stacks.Sites.sectionIdeal (ι j) (op W)).FG) ∧
              Presheaf.IsLocallySurjective (SmallEtale.topology B S hS Y.1) f.right.hom ∧
              (∀ (U : (SmallEtale B S hS Y.1)ᵒᵖ) (a : ℬ.right.obj.obj U),
                  (f.right.hom.app U).hom a = 0 →
                    Stacks.Sites.memSieve (O := ℬ.right) ι a ∈
                      SmallEtale.topology B S hS Y.1 U.unop) ∧
              ∃ j, (ℬ.idealQuotient (ι j)).IsIntegral) :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (D : I ⥤ QuasicoherentAlgebra B S hS Y) (φ : D ⟶ (Functor.const I).obj A),
      Nonempty (IsColimit (Cocone.mk A φ)) ∧
      (∀ i, (D.obj i).obj.IsFinite ∧ (D.obj i).obj.IsFinitePresentation) ∧
      ∀ i j (h : i ≤ j), Presheaf.IsLocallySurjective
        (SmallEtale.topology B S hS Y.obj) (D.map (homOfLE h)).hom.right.hom := by
  refine exists_directed_isFinite_isFinitePresentation_locallySurjective B S hS Y A hqc hqs hA
    (fun h₁ h₂ h₃ => ?_)
  obtain ⟨ℬ, f, J, instJ, hfilt, ι, hι, hkill, hBqc, hBfp, hIqc, hfg, hsurj, hmem, hint⟩ :=
    hdata h₁ h₂ h₃
  have hqcoh : ∀ j, (ℬ.idealQuotient (ι j)).IsQuasicoherent := fun j =>
    AlgebraSheaf.isQuasicoherent_idealQuotient ℬ (ι j) hBqc (hIqc j)
  exact ⟨ℬ, f, J, instJ, hfilt, ι, hι, hkill, hqcoh,
    fun j => AlgebraSheaf.isFinitePresentation_idealQuotient ℬ (ι j) hBqc (hIqc j) hBfp
      (hfg j), hint,
    nonempty_isColimit_idealQuotientQcohCocone_of_locally ℬ ι hι A f hkill hqcoh hsurj hmem⟩

end AlgebraicGeometry.Space

end
