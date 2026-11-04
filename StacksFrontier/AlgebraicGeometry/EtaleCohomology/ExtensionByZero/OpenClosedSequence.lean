module

public import Mathlib.CategoryTheory.Adjunction.Triple
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
public import Mathlib.CategoryTheory.Sites.Point.Comap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedImmersionsPushforward.SetSheafEssentialImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.Exactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtalePointUniverse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleStalkBaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The short exact sequence of a closed subscheme and its open complement

Let `X` be a scheme, let `i : Z ⟶ X` be a closed immersion and let `j : U ⟶ X` be an open
immersion whose image is the complement of the image of `i`.  For every abelian sheaf `F` on the
small étale site of `X` the counit of `j_! ⊣ j^{-1}` and the unit of `i^{-1} ⊣ i_*` fit into a
short exact sequence
`0 → j_! j^{-1} F → F → i_* i^{-1} F → 0`
of abelian sheaves on `X_étale`.

## Main definitions

* `Stacks.EtaleCohomology.etaleRestrictionAbelianDirectImageAdj`: for an étale morphism `j`,
  restriction `j^{-1}` is left adjoint to the direct image `j_*` built from base change along
  `j`.
* `Stacks.EtaleCohomology.etaleAbelianInverseImageRestrictionIso`: consequently, for an étale
  morphism the sheafified inverse image along base change agrees with restriction.
* `Stacks.EtaleCohomology.etaleAbelianInverseImageSheafFiberIso`: the stalk of an inverse image
  at a geometric point is the stalk of the original sheaf at the image geometric point.
* `CategoryTheory.GrothendieckTopology.Point.isoOfFiberIso` and
  `CategoryTheory.GrothendieckTopology.Point.sheafFiberIso`: an isomorphism of fibre functors
  is an isomorphism of points of a site, and isomorphic points have isomorphic stalk functors.

## Main results

* `Stacks.EtaleCohomology.shortExact_extensionByZero_etaleAbelianDirectImage`: **Stacks Project,
  Tag 095L**, the short exact sequence `0 → j_! j^{-1} F → F → i_* i^{-1} F → 0`.
* `Stacks.EtaleCohomology.extensionByZero_counit_comp_inverseImage_unit`: the two canonical maps
  compose to zero.
* `Stacks.EtaleCohomology.isIso_of_isIso_etaleAbelianInverseImage`: inverse image to the closed
  part and to the open part jointly reflect isomorphisms of abelian sheaves on `X_étale`.
* `Stacks.EtaleCohomology.isZero_etaleRestriction_etaleAbelianDirectImage` and
  `Stacks.EtaleCohomology.isZero_etaleAbelianInverseImage_extensionByZero`: the restriction to
  `U` of a direct image from `Z` vanishes, and so does the inverse image to `Z` of an extension
  by zero from `U`.

## Implementation notes

The two arrows are the adjunction maps, so there is nothing to choose: the left one is
`(extensionByZeroAdj j).counit` and the right one is
`(etaleAbelianInverseImageDirectImageAdj i).unit`, and both are natural in the sheaf.  The
sequence is stated as an existential over the proof that the composite vanishes, so that the
short complex it refers to is the one built from exactly those two arrows.

The source checks exactness on stalks at geometric points.  Here the stalkwise argument is
packaged once, as the statement that the two inverse images `i^{-1}` and `j^{-1}` jointly reflect
isomorphisms: every point of `X` lies in the image of `i` or in the image of `j`, so the
separable closures of the residue fields of `Z` and of `U` give a family of geometric points of
`X` covering `X`, which is conservative by
`AlgebraicGeometry.Scheme.isConservative_pointSmallEtale_ulift`, and the stalk of an inverse
image is the stalk at the image point.  Both inverse images are exact, so
`CategoryTheory.JointlyReflectIsomorphisms.shortExact_iff` reduces short exactness to short
exactness after `i^{-1}` and after `j^{-1}`.  Each of those two sequences *splits*, which is why
no homology computation is needed: after `i^{-1}` the left term vanishes and the right map is
invertible because `i_*` is fully faithful; after `j^{-1}` the right term vanishes and the left
map is invertible because `j_!` is fully faithful.

Full faithfulness of `j_!` is read off the adjoint triple `j_! ⊣ j^{-1} ⊣ j_*`: the unit of the
first adjunction is invertible exactly when the counit of the second is, and the latter is
`Stacks.EtaleCohomology.etaleDirectImageAdj_counit_isIso`, available because an open immersion is
a monomorphism.  Full faithfulness of `i_*` comes from base change along a closed immersion being
cover dense and locally full, which this library has for sheaves of sets and which, being a
property of the site functor, applies verbatim to abelian coefficients.

Two readings of `j^{-1}` occur, and the file identifies them.  In the statement of the sequence
`j^{-1}` is restriction, i.e. precomposition with composition by `j`, which is the inverse image
of an *étale* morphism; the stalk machinery, on the other hand, is available for the sheafified
inverse image along base change, which is the inverse image of an *arbitrary* morphism.  They
agree because both are left adjoints of the same direct image: that is
`etaleAbelianInverseImageRestrictionIso`, whose input is the site-level adjunction
`AlgebraicGeometry.Scheme.Etale.smallEtaleComposeBaseChangeAdj` between composition with `j` and
base change along `j`.

The vanishing statements come from the same geometric fact, that an étale `U`-scheme has empty
base change to `Z`: a sheaf has zero sections over an object of the small étale site whose
underlying scheme is empty, because the empty sieve covers such an object.

## References

* [Stacks Project, Tag 095L](https://stacks.math.columbia.edu/tag/095L)
* [Stacks Project, Tag 03S5](https://stacks.math.columbia.edu/tag/03S5)
* [Stacks Project, Tag 04CA](https://stacks.math.columbia.edu/tag/04CA)
* [Stacks Project, Tag 04FX](https://stacks.math.columbia.edu/tag/04FX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale

universe w u v

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type*} [Category* C] {J : GrothendieckTopology C}

/-- An isomorphism of fibre functors is an isomorphism of points of a site.  Morphisms of points
run opposite to morphisms of fibre functors, so the direction is reversed. -/
def isoOfFiberIso {Φ Ψ : Point.{w} J} (e : Φ.fiber ≅ Ψ.fiber) : Ψ ≅ Φ where
  hom := ⟨e.hom⟩
  inv := ⟨e.inv⟩
  hom_inv_id := by ext; simp
  inv_hom_id := by ext; simp

/-- Isomorphic points of a site have isomorphic stalk functors on sheaves. (Mathlib's
`Point.sheafFiberMapIso` is a different statement: the fibre functor of a point transported
along a continuous cocontinuous functor of sites.) -/
def sheafFiberIso {Φ Ψ : Point.{w} J} (ε : Ψ ≅ Φ)
    (A : Type*) [Category* A] [HasColimitsOfSize.{w, w} A] :
    Φ.sheafFiber (A := A) ≅ Ψ.sheafFiber where
  hom := ε.hom.sheafFiber
  inv := ε.inv.sheafFiber
  hom_inv_id := by rw [← Hom.sheafFiber_comp, ε.inv_hom_id, Hom.sheafFiber_id]
  inv_hom_id := by rw [← Hom.sheafFiber_comp, ε.hom_inv_id, Hom.sheafFiber_id]

end CategoryTheory.GrothendieckTopology.Point

namespace Stacks.EtaleCohomology

/-! ### Stalks of an inverse image -/

/-- The stalk at a geometric point `s` of `Y` of the inverse image along `f : Y ⟶ X` of an
abelian sheaf on the small étale site of `X` is the stalk of that sheaf at the image geometric
point `s ≫ f`, naturally in the sheaf.

A lift of `s` to the base change `V ×_X Y` of an étale `X`-scheme `V` is the same thing as a lift
of `s ≫ f` to `V`, which identifies the fibre functor of `s ≫ f` with base change followed by the
fibre functor of `s`; the comparison is that identification transported through
`CategoryTheory.GrothendieckTopology.Point.sheafFiberComapIso`. -/
@[sga "4 VIII 3.4" "abelian sheaves", sga "4½ Arcata 2.3.3"]
def etaleAbelianInverseImageSheafFiberIso {Y X : Scheme.{u}} (f : Y ⟶ X)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y) :
    etaleAbelianInverseImage.{u, v} f ⋙
        ((pointSmallEtale s).ulift.{max (u + 1) v}).sheafFiber ≅
      ((pointSmallEtale (s ≫ f)).ulift.{max (u + 1) v}).sheafFiber := by
  let G := smallEtaleBaseChange f
  let Φ := (pointSmallEtale s).ulift.{max (u + 1) v}
  have hG : CoverPreserving X.smallEtaleTopology Y.smallEtaleTopology G :=
    CoverPreserving.of_isContinuous _ _ _
  let _ : InitiallySmall.{max (u + 1) v} (G ⋙ Φ.fiber).Elements :=
    initiallySmall_of_essentiallySmall _
  let e : ((pointSmallEtale (s ≫ f)).ulift.{max (u + 1) v}).fiber ≅ (Φ.comap G hG).fiber :=
    Functor.isoWhiskerRight (pointSmallEtaleBaseChangeFiberIso f s)
        uliftFunctor.{max (u + 1) v, u} ≪≫
      Functor.associator _ _ _
  exact Functor.isoWhiskerRight
      (Functor.sheafPullbackConstruction.sheafPullbackIso G
        AddCommGrpCat.{max (u + 1) v} X.smallEtaleTopology Y.smallEtaleTopology).symm
      Φ.sheafFiber ≪≫
    (Φ.sheafFiberComapIso G hG AddCommGrpCat.{max (u + 1) v}).symm ≪≫
    (GrothendieckTopology.Point.sheafFiberIso
      (GrothendieckTopology.Point.isoOfFiberIso e) AddCommGrpCat.{max (u + 1) v}).symm

/-- A map of abelian sheaves on the small étale site of `X` whose inverse image along `f : Y ⟶ X`
is invertible has invertible stalk at the image `s ≫ f` of every geometric point `s` of `Y`. -/
theorem isIso_sheafFiber_map_of_isIso_etaleAbelianInverseImage {Y X : Scheme.{u}} (f : Y ⟶ X)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y)
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}} (γ : F ⟶ G)
    [IsIso ((etaleAbelianInverseImage.{u, v} f).map γ)] :
    IsIso (((pointSmallEtale (s ≫ f)).ulift.{max (u + 1) v}).sheafFiber.map γ) := by
  refine (NatIso.isIso_map_iff (etaleAbelianInverseImageSheafFiberIso.{u, v} f s) γ).mp ?_
  rw [Functor.comp_map]
  infer_instance

/-! ### Sections over an empty object -/

/-- The empty sieve covers an object of the small étale site whose underlying scheme is empty:
the empty family of arrows is jointly surjective onto an empty space. -/
theorem bot_mem_smallEtaleTopology_of_isEmpty {X : Scheme.{u}} (V : X.Etale)
    (hV : IsEmpty V.left) : (⊥ : Sieve V) ∈ X.smallEtaleTopology V := by
  have hbot : Sieve.ofArrows (fun j : PEmpty.{1} ↦ PEmpty.elim j)
      (fun j : PEmpty.{1} ↦ PEmpty.elim j) = (⊥ : Sieve V) := by
    simp [Sieve.ofArrows, Presieve.ofArrows_of_isEmpty]
  rw [← hbot, Scheme.ofArrows_mem_smallEtaleTopology_iff]
  ext x
  simp [hV.false x]

/-- An abelian sheaf on the small étale site has zero sections over an object whose underlying
scheme is empty. -/
theorem isZero_sections_of_isEmpty {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (V : X.Etale)
    (hV : IsEmpty V.left) : IsZero (F.obj.obj (op V)) :=
  (F.isTerminalOfBotCover V (bot_mem_smallEtaleTopology_of_isEmpty V hV)).isZero

/-- An abelian sheaf on the small étale site all of whose groups of sections vanish is zero. -/
theorem isZero_of_forall_isZero_sections {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hF : ∀ V : X.Etale, IsZero (F.obj.obj (op V))) : IsZero F :=
  IsZero.of_full_of_faithful_of_isZero (sheafToPresheaf _ _) F
    ((Functor.isZero_iff _).2 fun V ↦ hF V.unop)

/-! ### Comparing the two inverse images along an étale morphism -/

/-- Restriction along an étale morphism `j : U ⟶ X` is left adjoint to the direct image along
`j` formed from base change.

Both functors are precomposition along a functor of small étale sites, and composition with `j`
is left adjoint to base change along `j`, so the adjunction of presheaf categories induced by
that site-level adjunction restricts to the full subcategories of sheaves. -/
def etaleRestrictionAbelianDirectImageAdj {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] :
    etaleRestriction.{u, v} j ⊣ etaleAbelianDirectImage.{u, v} j :=
  ((smallEtaleComposeBaseChangeAdj j).op.whiskerLeft
      AddCommGrpCat.{max (u + 1) v}).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf _ _) (fullyFaithfulSheafToPresheaf _ _)
    (Iso.refl _) (Iso.refl _)

/-- For an étale morphism `j : U ⟶ X` the two readings of `j^{-1}` on abelian sheaves agree: the
sheafified inverse image along base change is isomorphic to restriction.  Both are left adjoints
of the direct image along base change. -/
def etaleAbelianInverseImageRestrictionIso {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] :
    etaleAbelianInverseImage.{u, v} j ≅ etaleRestriction.{u, v} j :=
  Adjunction.leftAdjointUniq (etaleAbelianInverseImageDirectImageAdj.{u, v} j)
    (etaleRestrictionAbelianDirectImageAdj.{u, v} j)

/-! ### The two canonical maps become invertible on the relevant part -/

/-- The direct image along a closed immersion is fully faithful on abelian sheaves: base change
along a closed immersion is cover dense and locally full. -/
def etaleAbelianDirectImageFullyFaithful {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] : (etaleAbelianDirectImage.{u, v} i).FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful _

/-- For a closed immersion `i`, the unit `F ⟶ i_* i^{-1} F` becomes invertible after applying
`i^{-1}`. -/
theorem isIso_etaleAbelianInverseImage_map_unit {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    IsIso ((etaleAbelianInverseImage.{u, v} i).map
      ((etaleAbelianInverseImageDirectImageAdj.{u, v} i).unit.app F)) :=
  inferInstance

/-- The unit of `j_! ⊣ j^{-1}` is an isomorphism for an étale monomorphism, equivalently for an
open immersion: in the adjoint triple `j_! ⊣ j^{-1} ⊣ j_*` the unit of the first adjunction is
invertible exactly when the counit of the second is. -/
instance isIso_extensionByZeroAdj_unit {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] [Mono j] :
    IsIso (extensionByZeroAdj.{u, v} j).unit :=
  (Adjunction.Triple.isIso_unit_iff_isIso_counit
    ⟨extensionByZeroAdj.{u, v} j, etaleDirectImageAdj.{u, v} j⟩).2 inferInstance

/-- For an étale monomorphism `j`, the counit `j_! j^{-1} F ⟶ F` becomes invertible after
applying `j^{-1}`. -/
theorem isIso_etaleRestriction_map_counit {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] [Mono j]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    IsIso ((etaleRestriction.{u, v} j).map ((extensionByZeroAdj.{u, v} j).counit.app F)) := by
  let ff := (extensionByZeroAdj.{u, v} j).fullyFaithfulLOfIsIsoUnit
  let _ := ff.full
  let _ := ff.faithful
  infer_instance

/-! ### The sequence of a closed subscheme and its open complement -/

section Complementary

variable {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X) [Etale j]
  (hij : Set.range j.base = (Set.range i.base)ᶜ)

include hij

/-- The base change to `Z` of an étale scheme over `U` is empty, `U` and `Z` having disjoint
images in `X`. -/
theorem isEmpty_smallEtaleBaseChange_smallEtaleCompose (W : U.Etale) :
    IsEmpty ((smallEtaleBaseChange i).obj ((smallEtaleCompose j).obj W)).left := by
  show IsEmpty (Limits.pullback (C := Scheme.{u}) (W.hom ≫ j) i)
  refine Scheme.isEmpty_pullback _ _ (Set.disjoint_left.2 ?_)
  rintro x ⟨w, rfl⟩ ⟨z, hz⟩
  exact hij.subset ⟨W.hom.base w, by simp⟩ ⟨z, hz⟩

/-- Restricting to `U` a direct image from `Z` gives zero: the sections of such a restriction
over an étale `U`-scheme are sections over an empty scheme. -/
theorem isZero_etaleRestriction_etaleAbelianDirectImage
    (G : Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    IsZero ((etaleRestriction.{u, v} j).obj ((etaleAbelianDirectImage.{u, v} i).obj G)) :=
  isZero_of_forall_isZero_sections _ fun W ↦
    isZero_sections_of_isEmpty G _ (isEmpty_smallEtaleBaseChange_smallEtaleCompose i j hij W)

/-- Any two maps from an extension by zero from `U` to a direct image from `Z` are equal, by the
adjunction `j_! ⊣ j^{-1}` and the vanishing of `j^{-1} i_*`. -/
private theorem extensionByZero_hom_ext_etaleAbelianDirectImage
    {A : Sheaf U.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}}
    {B : Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}}
    (f g : (extensionByZero.{u, v} j).obj A ⟶ (etaleAbelianDirectImage.{u, v} i).obj B) :
    f = g :=
  ((extensionByZeroAdj.{u, v} j).homEquiv _ _).injective
    ((isZero_etaleRestriction_etaleAbelianDirectImage i j hij _).eq_of_tgt _ _)

/-- The inverse image to `Z` of an extension by zero from `U` is zero: by the two adjunctions it
receives no nonzero map, since restricting to `U` a direct image from `Z` already vanishes. -/
theorem isZero_etaleAbelianInverseImage_extensionByZero
    (G : Sheaf U.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    IsZero ((etaleAbelianInverseImage.{u, v} i).obj ((extensionByZero.{u, v} j).obj G)) := by
  rw [IsZero.iff_id_eq_zero]
  exact ((etaleAbelianInverseImageDirectImageAdj.{u, v} i).homEquiv _ _).injective
    (extensionByZero_hom_ext_etaleAbelianDirectImage i j hij _ _)

/-- The composite `j_! j^{-1} F ⟶ F ⟶ i_* i^{-1} F` of the two canonical maps is zero: it is a map
from an extension by zero from `U` to a direct image from `Z`. -/
theorem extensionByZero_counit_comp_inverseImage_unit
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    (extensionByZeroAdj.{u, v} j).counit.app F ≫
      (etaleAbelianInverseImageDirectImageAdj.{u, v} i).unit.app F = 0 :=
  extensionByZero_hom_ext_etaleAbelianDirectImage i j hij _ _

/-- The coefficient fields of the family of geometric points of `X` indexed by the points of `Z`
and of `U`: a separable closure of the residue field there. -/
public def complementCoefficients (Z U : Scheme.{u}) : Z ⊕ U → Type u
  | .inl z => SeparableClosure (Z.residueField z)
  | .inr w => SeparableClosure (U.residueField w)

/-- Each coefficient type `complementCoefficients Z U a` is a field. -/
public instance (Z U : Scheme.{u}) (a : Z ⊕ U) : Field (complementCoefficients Z U a) := by
  cases a <;> exact inferInstanceAs (Field (SeparableClosure _))

/-- Each coefficient type `complementCoefficients Z U a` is separably closed. -/
public instance (Z U : Scheme.{u}) (a : Z ⊕ U) :
    IsSepClosed (complementCoefficients Z U a) := by
  cases a <;> exact inferInstanceAs (IsSepClosed (SeparableClosure _))

/-- The family of geometric points of `X` indexed by the points of `Z` and of `U`, obtained by
pushing the residue geometric points forward along `i` and along `j`. -/
public def complementPoint :
    ∀ a : Z ⊕ U, Spec (.of (complementCoefficients Z U a)) ⟶ X
  | .inl z => residueGeometricPoint Z z ≫ i
  | .inr w => residueGeometricPoint U w ≫ j

omit [Etale j] in
/-- The geometric points of `complementPoint` cover `X`: a point of `X` lies in the image of `i`
or, failing that, in its complement, which is the image of `j`. -/
public theorem iUnion_range_complementPoint :
    ⋃ a, Set.range (complementPoint i j a) = Set.univ := by
  refine Set.eq_univ_of_forall fun x ↦ ?_
  by_cases hx : x ∈ Set.range i.base
  · obtain ⟨z, rfl⟩ := hx
    refine Set.mem_iUnion.2 ⟨Sum.inl z, default, ?_⟩
    show i.base ((residueGeometricPoint Z z).base default) = i.base z
    rw [residueGeometricPoint_apply]
  · obtain ⟨w, rfl⟩ : x ∈ Set.range j.base := by rwa [hij]
    refine Set.mem_iUnion.2 ⟨Sum.inr w, default, ?_⟩
    show j.base ((residueGeometricPoint U w).base default) = j.base w
    rw [residueGeometricPoint_apply]

omit hij [Etale j] in
/-- A map of abelian sheaves on `X_étale` that becomes invertible after `i^{-1}` and after
`j^{-1}` has invertible stalk at every geometric point of the family `complementPoint`. -/
theorem isIso_sheafFiber_map_complementPoint
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}} (γ : F ⟶ G)
    [IsIso ((etaleAbelianInverseImage.{u, v} i).map γ)]
    [IsIso ((etaleAbelianInverseImage.{u, v} j).map γ)] (a : Z ⊕ U) :
    IsIso (((pointSmallEtale
      (complementPoint i j a)).ulift.{max (u + 1) v}).sheafFiber.map γ) := by
  cases a with
  | inl z =>
    exact isIso_sheafFiber_map_of_isIso_etaleAbelianInverseImage.{u, v} i
      (residueGeometricPoint Z z) γ
  | inr w =>
    exact isIso_sheafFiber_map_of_isIso_etaleAbelianInverseImage.{u, v} j
      (residueGeometricPoint U w) γ

omit [Etale j] in
/-- Inverse image to the closed part and inverse image to the open part jointly reflect
isomorphisms of abelian sheaves on the small étale site of `X`.

The residue geometric points of `Z` and of `U`, pushed forward to `X`, form a conservative family
of points of `X_étale`, and the stalk of an inverse image at such a point is the stalk of the
original sheaf there. -/
theorem isIso_of_isIso_etaleAbelianInverseImage
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}} (γ : F ⟶ G)
    [IsIso ((etaleAbelianInverseImage.{u, v} i).map γ)]
    [IsIso ((etaleAbelianInverseImage.{u, v} j).map γ)] : IsIso γ := by
  have hP : (ObjectProperty.ofObj (fun a ↦ (pointSmallEtale
      (complementPoint i j a)).ulift.{max (u + 1) v})).IsConservativeFamilyOfPoints :=
    Scheme.isConservative_pointSmallEtale_ulift _ (iUnion_range_complementPoint i j hij)
  have happ : ∀ p : (ObjectProperty.ofObj (fun a ↦ (pointSmallEtale
      (complementPoint i j a)).ulift.{max (u + 1) v})).FullSubcategory,
      IsIso (p.obj.sheafFiber.map γ) := by
    rintro ⟨_, ⟨a⟩⟩
    exact isIso_sheafFiber_map_complementPoint i j γ a
  exact (hP.jointlyReflectIsomorphisms AddCommGrpCat.{max (u + 1) v}).isIso γ

end Complementary

/-- **Stacks Project, Tag 095L.** Let `X` be a scheme, let `i : Z ⟶ X` be a closed immersion and
let `j : U ⟶ X` be an open immersion whose image is the complement of the image of `i`.  For
every abelian sheaf `F` on the small étale site of `X` the counit of `j_! ⊣ j^{-1}` and the unit
of `i^{-1} ⊣ i_*` form a short exact sequence
`0 → j_! j^{-1} F → F → i_* i^{-1} F → 0`
of abelian sheaves on `X_étale`. -/
@[stacks 095L, sga "4 VIII 6.5" "partial"]
theorem shortExact_extensionByZero_etaleAbelianDirectImage {Z U X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
    (hij : Set.range j.base = (Set.range i.base)ᶜ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    ∃ h : (extensionByZeroAdj.{u, v} j).counit.app F ≫
        (etaleAbelianInverseImageDirectImageAdj.{u, v} i).unit.app F = 0,
      (ShortComplex.mk ((extensionByZeroAdj.{u, v} j).counit.app F)
        ((etaleAbelianInverseImageDirectImageAdj.{u, v} i).unit.app F) h).ShortExact := by
  refine ⟨extensionByZero_counit_comp_inverseImage_unit i j hij F, ?_⟩
  let L : (b : Bool) → Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⥤
      Sheaf (smallEtaleTopology (if b then U else Z)) AddCommGrpCat.{max (u + 1) v} := fun
    | false => etaleAbelianInverseImage.{u, v} i
    | true => etaleAbelianInverseImage.{u, v} j
  have _ : ∀ b, PreservesFiniteLimits (L b) := fun b ↦ by cases b <;> infer_instance
  have _ : ∀ b, PreservesFiniteColimits (L b) := fun b ↦ by cases b <;> infer_instance
  have hL : JointlyReflectIsomorphisms L := by
    refine ⟨fun γ hγ ↦ ?_⟩
    have _ : IsIso ((etaleAbelianInverseImage.{u, v} i).map γ) := hγ false
    have _ : IsIso ((etaleAbelianInverseImage.{u, v} j).map γ) := hγ true
    exact isIso_of_isIso_etaleAbelianInverseImage i j hij γ
  refine (hL.shortExact_iff _).2 fun b ↦ ?_
  cases b
  · exact (ShortComplex.Splitting.ofIsZeroOfIsIso _
      (isZero_etaleAbelianInverseImage_extensionByZero i j hij _)
      (isIso_etaleAbelianInverseImage_map_unit.{u, v} i F)).shortExact
  · refine (ShortComplex.Splitting.ofIsIsoOfIsZero _ ?_ ?_).shortExact
    · exact (NatIso.isIso_map_iff (etaleAbelianInverseImageRestrictionIso.{u, v} j)
        ((extensionByZeroAdj.{u, v} j).counit.app F)).mpr
          (isIso_etaleRestriction_map_counit.{u, v} j F)
    · exact IsZero.of_iso (isZero_etaleRestriction_etaleAbelianDirectImage i j hij _)
        ((etaleAbelianInverseImageRestrictionIso.{u, v} j).app _)

end Stacks.EtaleCohomology

end
