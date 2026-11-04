module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsStandardTopologies

/-!
# Extending a sheaf for one of the five topologies from a full subcategory of schemes

Let `τ` be one of the five topologies admitting standard affine coverings — Zariski, étale,
smooth, syntomic and fppf — let `S` be a scheme and let `𝒞` be a full subcategory of `Sch/S`
satisfying conditions (1) and (2) of Stacks 0EUW; the big site `(Sch/S)_τ` is such a
subcategory. Let `F : 𝒞ᵒᵖ ⥤ Set` be a `τ`-sheaf, that is, a functor satisfying the sheaf
condition for every `τ`-covering of an object of `𝒞` by objects of `𝒞`. This file shows that
`F` then satisfies conditions (a) and (c) of Stacks 0EUW and 0GDW, and deduces that the
extension `F' = AlgebraicGeometry.ExtendingFunctors.extension` of `F` to all schemes over `S`
satisfies the sheaf condition for all `τ`-coverings — unconditionally for `τ = Zariski`, and for
a general `τ` from the restricted sheaf condition of the extension, which is proved above this
file in the import order and is therefore carried here as a hypothesis.

## The two conditions

Condition (a) — the Zariski sheaf condition on `𝒞` — follows because a jointly surjective family
of open immersions is a `τ`-covering for every one of the five topologies: an open immersion is
étale, hence smooth, syntomic, and flat and locally of finite presentation. The passage is not
formal, because condition (a) is stated in the shape forced by the footnote of Stacks 0EUW: the
fibre products of a Zariski covering of an object of `𝒞` by objects of `𝒞` need not lie in `𝒞`,
so the compatibility of a family of sections is only asked for on a covering of each fibre
product by objects of `𝒞`, whereas `CategoryTheory.Presieve.IsSheafFor` asks for it on every
object of `𝒞` mapping to two members. Recovering the latter from the former is the content of
`AlgebraicGeometry.ExtendingFunctors.isZariskiSheafOnSubcategory_of_isCoveringSheafOnSubcategory`:
a morphism into two members of the covering factors, over each affine open of its source small
enough, through a member of the given covering of the fibre product, and those affine opens lie
in `𝒞` by condition (1), so the two restrictions agree locally and therefore agree, by the
separatedness half of the `τ`-sheaf condition for that affine open covering.

Condition (c) is immediate, a standard `τ`-covering of an affine object being a `τ`-covering.

## The Zariski case is unconditional

For `τ = Zariski` the conclusion needs nothing beyond condition (a): a Zariski sheaf on `Sch/S`
in the sense of `AlgebraicGeometry.ExtendingFunctors.IsZariskiSheaf` — sections over an object
are families of sections over the members of an open covering agreeing on the pairwise
intersections — already satisfies `CategoryTheory.Presieve.IsSheafFor` for every jointly
surjective family of open immersions, which is exactly a Zariski covering. This is
`AlgebraicGeometry.ExtendingFunctors.isCoveringSheaf_zariski_of_isZariskiSheaf`, proved by
identifying each member of the family with the open subobject which is its image, choosing one
member through each point of the target so as to index the resulting open covering by the points
of the target, and gluing.

## Main definitions

* `AlgebraicGeometry.ExtendingFunctors.IsCoveringSheafOnSubcategory`: the `τ`-sheaf condition for
  a functor on a full subcategory of `Sch/S`.
* `AlgebraicGeometry.ExtendingFunctors.overOpenIso`: the identification of the source of an open
  immersion of `Sch/S` with the open subobject which is its image.

## Main results

* `AlgebraicGeometry.ExtendingFunctors.isZariskiSheafOnSubcategory_of_isCoveringSheafOnSubcategory`
  and
  `ExtendingFunctors.isStandardAffineSheafOnSubcategory_of_isCoveringSheafOnSubcategory`:
  a `τ`-sheaf on the subcategory satisfies conditions (a) and (c).
* `AlgebraicGeometry.ExtendingFunctors.isSheafFor_extension_of_isCoveringSheafOnSubcategory` and
  `AlgebraicGeometry.ExtendingFunctors.isSheafFor_extension_of_memUpToIso`: the extension
  satisfies the sheaf condition for the `τ`-coverings of an object of `𝒞` — or of an object of
  `Sch/S` isomorphic to one — by objects of `𝒞`, or by objects isomorphic to objects of `𝒞`.
* `AlgebraicGeometry.ExtendingFunctors.isSheafFor_ofArrows_of_isZariskiSheaf` and
  `AlgebraicGeometry.ExtendingFunctors.isCoveringSheaf_zariski_of_isZariskiSheaf`: a Zariski
  sheaf on `Sch/S` is a sheaf for every covering by open immersions.
* `AlgebraicGeometry.ExtendingFunctors.isCoveringSheaf_zariski_extension`: **Stacks 0EUX for
  `τ = Zariski`**, with no further hypothesis.
* `AlgebraicGeometry.ExtendingFunctors.isCoveringSheaf_extension_of_isCoveringSheafOnSubcategory`:
  the conclusion of Stacks 0EUX, uniformly in `τ`, with the sheaf condition of the extension for
  the standard `τ`-coverings of the affine objects of `Sch/S` lying over an affine open of `S`
  carried as a hypothesis. That hypothesis is redundant; it is discharged in
  `StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsStandardAffineInterchange`, which
  imports this file and where **Stacks 0EUX** is therefore stated unconditionally, for all five
  topologies, as
  `AlgebraicGeometry.ExtendingFunctors.isCoveringSheaf_extension_of_isCoveringSheafOnSubcategory'`.

## Implementation notes

The statement of the source takes `𝒞 = (Sch/S)_τ`; what its proof uses of that choice is that
`𝒞` satisfies conditions (1) and (2) of Stacks 0EUW and that a standard `τ`-covering is
tautologically equivalent to a covering in `𝒞`. Everything below is therefore stated for an
arbitrary full subcategory satisfying (1) and (2), as are the carriers of Stacks 0EUW and 0GDW in
this library; the `τ`-sheaf condition is asked for directly, on the covering families of `𝒞`,
rather than through a Grothendieck topology and tautological equivalence of coverings.

**Why a redundant hypothesis is carried here.** The source's proof of Stacks 0EUX is Stacks 0GDW
applied with `𝒞 = (Sch/S)_τ`, and Stacks 0GDW is formalized in
`StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsStandardTopologies` only from its
*standard affine case* onwards: the deduction of the sheaf condition of the extension for the
standard `τ`-coverings of an arbitrary affine object of `Sch/S` lying over an affine open of `S`
— which writes that object as a directed limit of affines of finite presentation (Stacks 00QN),
descends the covering to a stage of the limit (Stacks 049N) and passes to the filtered colimit —
is not carried out there. It *is* formalized in this library, as
`AlgebraicGeometry.ExtendingFunctors.isStandardAffineSheaf_extension` in
`StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsStandardAffineInterchange`; but that
file imports this one, so the deduction cannot be cited here. The statement for a general `τ`
below therefore carries it as the hypothesis `hstd`, redundantly, and the unconditional form of
Stacks 0EUX — `hstd` discharged — is
`AlgebraicGeometry.ExtendingFunctors.isCoveringSheaf_extension_of_isCoveringSheafOnSubcategory'`
in that file. The import order is the only gap between the statement proved here and the
source's. For `τ = Zariski` no such hypothesis is needed, because an arbitrary standard Zariski
covering is an open covering and the extension is a Zariski sheaf.

**What this file contributes towards that deduction.** Writing the affine object as a directed
limit of objects of `𝒞` is
`AlgebraicGeometry.ExtendingFunctors.exists_lfpPresentation_factorization`, and descending the
standard `τ`-covering to a stage is
`AlgebraicGeometry.exists_isStandardCovering_of_isLimit`. The sheaf condition of the extension
*at a stage* is `isSheafFor_extension_of_memUpToIso` below: the stages and the base changes to
them of the members of the descended covering are affine and of finite presentation over an
affine open of `S`, hence isomorphic to objects of `𝒞` by condition (2). What remains — the
interchange of the sheaf condition, an equalizer of finite products, the index type of a
standard covering being finite, with the filtered colimit computing the extension at the limit
of the stages — is carried out in
`StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsStandardAffineInterchange`.

## References

* [Stacks Project, Tag 0EUX](https://stacks.math.columbia.edu/tag/0EUX)
* [Stacks Project, Tag 0GDW](https://stacks.math.columbia.edu/tag/0GDW)
* [Stacks Project, Tag 0EUW](https://stacks.math.columbia.edu/tag/0EUW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ExtendingFunctors

universe w u v

variable {S : Scheme.{u}}

/-! ### Open immersions are coverings for each of the five topologies -/

/-- An open immersion has the property of morphisms defining each of the five topologies: it is
étale, hence smooth, syntomic, and flat and locally of finite presentation. -/
lemma coveringMorphismProperty_of_isOpenImmersion (τ : CoveringTopology) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] : coveringMorphismProperty τ f := by
  cases τ with
  | fppf => exact ⟨inferInstance, inferInstance⟩
  | syntomic => exact syntomic_of_etale f
  | smooth => infer_instance
  | etale => infer_instance
  | zariski => infer_instance

/-- A jointly surjective family of open immersions of `Sch/S` is a `τ`-covering. -/
lemma ofArrows_mem_coveringPrecoverage_of_isOpenImmersion (τ : CoveringTopology) {X : Over S}
    {ι : Type v} (Y : ι → Over S) (f : ∀ i, Y i ⟶ X)
    (hf : ∀ i, IsOpenImmersion (f i).left)
    (hcov : ⨆ i, (f i).left.opensRange = ⊤) :
    Presieve.ofArrows Y f ∈ coveringPrecoverage S τ X := by
  rw [ofArrows_mem_coveringPrecoverage_iff]
  refine ⟨fun x => ?_, fun i => ?_⟩
  · have hx : x ∈ (⨆ i, (f i).left.opensRange) := by rw [hcov]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact ⟨i, hi⟩
  · have := hf i
    exact coveringMorphismProperty_of_isOpenImmersion τ (f i).left

/-! ### The `τ`-sheaf condition on a full subcategory -/

/-- **The `τ`-sheaf condition for a functor on a full subcategory of `Sch/S`.** For every
`τ`-covering `{Y i ⟶ X}` of an object of the subcategory by objects of the subcategory, the sheaf
condition holds.

The covering condition is the one of `AlgebraicGeometry.ExtendingFunctors.IsCoveringSheaf`, read
on the underlying objects of `Sch/S`; the sheaf condition is
`CategoryTheory.Presieve.IsSheafFor` inside the subcategory, so the compatibility of a family of
sections is tested on the objects of the subcategory mapping to two members of the covering.
Taking the subcategory to be the big site `(Sch/S)_τ`, this is the hypothesis of Stacks 0EUX on
`F`. -/
def IsCoveringSheafOnSubcategory (τ : CoveringTopology) (P : ObjectProperty (Over S))
    (F : P.FullSubcategoryᵒᵖ ⥤ Type w) : Prop :=
  ∀ {ι : Type v} (X : P.FullSubcategory) (Y : ι → P.FullSubcategory) (f : ∀ i, Y i ⟶ X),
    Presieve.ofArrows (fun i => (Y i).obj) (fun i => P.ι.map (f i))
        ∈ coveringPrecoverage S τ X.obj →
      (Presieve.ofArrows Y f).IsSheafFor F

variable {P : ObjectProperty (Over S)}

/-- **Separatedness of a `τ`-sheaf on the subcategory for an open covering.** Two sections over an
object of the subcategory which agree on the members of a covering of it by open immersions out
of objects of the subcategory are equal. -/
lemma ext_of_isCoveringSheafOnSubcategory {τ : CoveringTopology}
    {F : P.FullSubcategoryᵒᵖ ⥤ Type w} (hF : IsCoveringSheafOnSubcategory.{w, u, v} τ P F)
    {X : P.FullSubcategory} {ι : Type v} (Y : ι → P.FullSubcategory) (f : ∀ i, Y i ⟶ X)
    (hfopen : ∀ i, IsOpenImmersion (P.ι.map (f i)).left)
    (hfcov : ⨆ i, (P.ι.map (f i)).left.opensRange = ⊤)
    (t t' : F.obj (op X)) (h : ∀ i, F.map (f i).op t = F.map (f i).op t') : t = t' := by
  refine (hF X Y f (ofArrows_mem_coveringPrecoverage_of_isOpenImmersion τ _ _
    hfopen hfcov)).isSeparatedFor.ext ?_
  rintro Z g ⟨i⟩
  exact h i

/-! ### Conditions (a) and (c) for a `τ`-sheaf on the subcategory -/

/-- A morphism of the subcategory whose image lies in the image of an open immersion of the
subcategory factors through it. -/
private noncomputable def subLift {A B C : P.FullSubcategory} (j : B ⟶ C)
    [IsOpenImmersion (P.ι.map j).left] (g : A ⟶ C)
    (h : Set.range (P.ι.map g).left.base ⊆ Set.range (P.ι.map j).left.base) : A ⟶ B :=
  ObjectProperty.homMk (Over.homMk
    (IsOpenImmersion.lift (P.ι.map j).left (P.ι.map g).left h)
    (by
      have h1 : (P.ι.map j).left ≫ C.obj.hom = B.obj.hom := Over.w (P.ι.map j)
      have h2 : (P.ι.map g).left ≫ C.obj.hom = A.obj.hom := Over.w (P.ι.map g)
      rw [← h1, IsOpenImmersion.lift_fac_assoc, h2]))

private lemma subLift_fac {A B C : P.FullSubcategory} (j : B ⟶ C)
    [IsOpenImmersion (P.ι.map j).left] (g : A ⟶ C)
    (h : Set.range (P.ι.map g).left.base ⊆ Set.range (P.ι.map j).left.base) :
    subLift j g h ≫ j = g := by
  refine P.ι.map_injective (Over.OverMorphism.ext ?_)
  rw [Functor.map_comp, Over.comp_left]
  exact IsOpenImmersion.lift_fac _ _ _

/-- An equation between composites in the subcategory gives one between the underlying schemes. -/
private lemma left_comp_eq_left_comp {A B C D : P.FullSubcategory} {α : A ⟶ B} {β : A ⟶ C}
    {γ : B ⟶ D} {δ : C ⟶ D} (h : α ≫ γ = β ≫ δ) :
    (P.ι.map α).left ≫ (P.ι.map γ).left = (P.ι.map β).left ≫ (P.ι.map δ).left :=
  congrArg (fun m => (P.ι.map m).left) h

/-- **Condition (a) of Stacks 0EUW holds for a `τ`-sheaf on the subcategory.** A jointly
surjective family of open immersions is a `τ`-covering, so the `τ`-sheaf condition gives both the
existence and the uniqueness of the glued section; what has to be supplied is the compatibility
of the family of sections on every object of the subcategory mapping to two members of the
covering, whereas condition (a) only gives it on the members of a covering of each fibre product
by objects of the subcategory.

The two restrictions of such an object agree locally: over an affine open of it small enough the
morphism to the first member factors through a member `U i j k` of the given covering of the
fibre product, and then so does the morphism to the second member, because the two agree after
composition with the monomorphism into the target. Those affine opens lie in the subcategory by
condition (1), and a section of the subcategory is separated for the covering by them, again
because it is a `τ`-covering. -/
theorem isZariskiSheafOnSubcategory_of_isCoveringSheafOnSubcategory (τ : CoveringTopology)
    (hP1 : HasAffineOpens P) {F : P.FullSubcategoryᵒᵖ ⥤ Type w}
    (hF : IsCoveringSheafOnSubcategory.{w, u, u} τ P F) :
    IsZariskiSheafOnSubcategory P F := by
  classical
  intro X ι Y f hfopen hfcov K U a b haopen hab hcov s hs
  have hcompat : ∀ (i j : ι) (A : P.FullSubcategory) (α : A ⟶ Y i) (β : A ⟶ Y j),
      α ≫ f i = β ≫ f j → F.map α.op (s i) = F.map β.op (s j) := by
    intro i j A α β hαβ
    have hαβ' := left_comp_eq_left_comp hαβ
    have key : ∀ z : A.obj.left, ∃ (k : K i j) (V : A.obj.left.Opens),
        IsAffineOpen V ∧ z ∈ V ∧
          V ≤ (P.ι.map α).left ⁻¹ᵁ (P.ι.map (a i j k)).left.opensRange := by
      intro z
      have hpt : (P.ι.map (f i)).left.base ((P.ι.map α).left.base z)
          = (P.ι.map (f j)).left.base ((P.ι.map β).left.base z) := by
        have h := congrArg (fun m : A.obj.left ⟶ X.obj.left => m.base z) hαβ'
        simpa using h
      have hz : (P.ι.map α).left.base z
          ∈ (P.ι.map (f i)).left ⁻¹ᵁ (P.ι.map (f j)).left.opensRange :=
        ⟨(P.ι.map β).left.base z, hpt.symm⟩
      rw [← hcov i j] at hz
      obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp hz
      obtain ⟨V, hVaff, hzV, hVle, -⟩ := exists_isAffineOverAffineOpen_nbhd A.obj z
        ((P.ι.map α).left ⁻¹ᵁ (P.ι.map (a i j k)).left.opensRange) hk
      exact ⟨k, V, hVaff, hzV, hVle⟩
    choose kz Vz hVzaff hzVz hVzle using key
    choose Az hAz eAz using fun z : A.obj.left => hP1 A.obj A.property ⟨Vz z, hVzaff z⟩
    have eB : ∀ z : A.obj.left, overOpen A.obj (Vz z) ≅
        (⟨Az z, hAz z⟩ : P.FullSubcategory).obj := fun z => (eAz z).some
    refine ext_of_isCoveringSheafOnSubcategory hF (fun z => ⟨Az z, hAz z⟩)
      (fun z => openSubHom A.property (eB z)) (fun z => inferInstance) ?_ _ _ fun z => ?_
    · refine le_antisymm le_top fun z _ => ?_
      refine TopologicalSpace.Opens.mem_iSup.mpr ⟨z, ?_⟩
      rw [opensRange_left_openSubHom]
      exact hzVz z
    · set g := openSubHom A.property (eB z) with hg
      have hrange : Set.range (P.ι.map (g ≫ α)).left.base
          ⊆ Set.range (P.ι.map (a i j (kz z))).left.base := by
        rintro _ ⟨y, rfl⟩
        have hy : (P.ι.map g).left.base y ∈ Vz z := by
          rw [← opensRange_left_openSubHom A.property (eB z)]
          exact ⟨y, rfl⟩
        have hy' := hVzle z hy
        refine Set.mem_of_eq_of_mem ?_ hy'
        rw [Functor.map_comp, Over.comp_left]
        simp
      set l := subLift (a i j (kz z)) (g ≫ α) hrange with hl
      have hla : l ≫ a i j (kz z) = g ≫ α := subLift_fac _ _ hrange
      have hlb : l ≫ b i j (kz z) = g ≫ β := by
        have hab' := left_comp_eq_left_comp (hab i j (kz z))
        have hla' := left_comp_eq_left_comp hla
        refine P.ι.map_injective (Over.OverMorphism.ext ?_)
        rw [Functor.map_comp, Functor.map_comp, Over.comp_left, Over.comp_left,
          ← cancel_mono (P.ι.map (f j)).left, Category.assoc, Category.assoc, ← hab',
          ← Category.assoc, hla', Category.assoc, hαβ']
      rw [map_map_apply, map_map_apply, ← hla, ← hlb, ← map_map_apply, ← map_map_apply,
        hs i j (kz z)]
  obtain ⟨t, ht⟩ := exists_section_of_isSheafFor_ofArrows Y f
    (hF X Y f (ofArrows_mem_coveringPrecoverage_of_isOpenImmersion τ _ _ hfopen hfcov)) s hcompat
  refine ⟨t, ht, fun t' ht' => ?_⟩
  exact ext_of_isCoveringSheafOnSubcategory hF Y f hfopen hfcov t' t
    fun i => (ht' i).trans (ht i).symm

/-- **Condition (c) of Stacks 0GDW holds for a `τ`-sheaf on the subcategory**, a standard
`τ`-covering of an affine object being a `τ`-covering. -/
theorem isStandardAffineSheafOnSubcategory_of_isCoveringSheafOnSubcategory
    (τ : CoveringTopology) {F : P.FullSubcategoryᵒᵖ ⥤ Type w}
    (hF : IsCoveringSheafOnSubcategory.{w, u, v} τ P F) :
    IsStandardAffineSheafOnSubcategory.{w, u, v} τ P F := by
  intro ι V hV _U _g _hg _hgfp W f hstd
  exact hF V W f (ofArrows_mem_coveringPrecoverage_of_isStandardCovering τ hV
    (fun i => (W i).obj) (fun i => P.ι.map (f i)) hstd)

/-! ### The extension is a sheaf for the coverings inside the subcategory -/

/-- Application of the naturality square of a natural transformation out of a restricted functor
to an element. -/
private lemma natTrans_apply {C D : Type*} [Category C] [Category D] (L : C ⥤ D)
    {G : Dᵒᵖ ⥤ Type w} {H : Cᵒᵖ ⥤ Type w} (θ : L.op ⋙ G ⟶ H) {A B : C} (g : A ⟶ B)
    (s : G.obj (op (L.obj B))) :
    θ.app (op A) (G.map (L.map g).op s) = H.map g.op (θ.app (op B) s) := by
  have h : ((L.op ⋙ G).map g.op ≫ θ.app (op A)) = θ.app (op B) ≫ H.map g.op :=
    θ.naturality g.op
  have h2 : ((L.op ⋙ G).map g.op ≫ θ.app (op A)) s = (θ.app (op B) ≫ H.map g.op) s := by rw [h]
  simpa using h2

/-- The property of morphisms defining each of the five topologies is invariant under composition
with an isomorphism. -/
lemma respectsIso_coveringMorphismProperty (τ : CoveringTopology) :
    (coveringMorphismProperty.{u} τ).RespectsIso :=
  have := isStableUnderBaseChange_coveringMorphismProperty.{u} τ
  inferInstance

/-- **Invariance of the `τ`-covering condition under isomorphism.** A family of arrows obtained
from a `τ`-covering by replacing the target and each source by an isomorphic object is again a
`τ`-covering. -/
lemma ofArrows_mem_coveringPrecoverage_of_iso (τ : CoveringTopology) {X X' : Over S} (e : X ≅ X')
    {κ : Type v} {W W' : κ → Over S} (d : ∀ i, W i ≅ W' i) (f : ∀ i, W i ⟶ X)
    (f' : ∀ i, W' i ⟶ X') (hd : ∀ i, (d i).hom ≫ f' i = f i ≫ e.hom)
    (h : Presieve.ofArrows W f ∈ coveringPrecoverage S τ X) :
    Presieve.ofArrows W' f' ∈ coveringPrecoverage S τ X' := by
  have hri := respectsIso_coveringMorphismProperty.{u} τ
  obtain ⟨hsurj, hprop⟩ := (ofArrows_mem_coveringPrecoverage_iff τ W f).mp h
  have hfac : ∀ i, f' i = (d i).inv ≫ f i ≫ e.hom := fun i => by
    rw [← hd i, Iso.inv_hom_id_assoc]
  rw [ofArrows_mem_coveringPrecoverage_iff]
  refine ⟨fun x => ?_, fun i => ?_⟩
  · obtain ⟨i, y, hy⟩ := hsurj (e.inv.left x)
    refine ⟨i, (d i).hom.left y, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hd i, Over.comp_left,
      Scheme.Hom.comp_apply, hy, ← Scheme.Hom.comp_apply, ← Over.comp_left, e.inv_hom_id]
    simp
  · have hiso₁ : IsIso ((d i).inv.left) :=
      inferInstanceAs (IsIso ((Over.forget S).map (d i).inv))
    have hiso₂ : IsIso (e.hom.left) := inferInstanceAs (IsIso ((Over.forget S).map e.hom))
    rw [hfac i, Over.comp_left, Over.comp_left]
    exact MorphismProperty.RespectsIso.precomp _ _ _
      (MorphismProperty.RespectsIso.postcomp _ _ _ (hprop i))

/-- **Invariance of the sheaf condition for a family of arrows under isomorphism.** Let two
families of arrows be given, with an isomorphism of their targets and, for each index, an
isomorphism of the sources commuting with the two members and the isomorphism of the targets. If
a functor satisfies the sheaf condition for the second family, it satisfies it for the first.

The sheaf condition for a family of arrows is a condition on the amalgamations of the families of
sections over its members, so transporting it amounts to transporting a section along each of the
given isomorphisms; no sieve or Grothendieck topology is involved. -/
theorem isSheafFor_ofArrows_of_iso {C : Type*} [Category C] {G : Cᵒᵖ ⥤ Type w} {X X' : C}
    (e : X ≅ X') {κ : Type*} {W W' : κ → C} (d : ∀ i, W i ≅ W' i) (f : ∀ i, W i ⟶ X)
    (f' : ∀ i, W' i ⟶ X') (hd : ∀ i, (d i).hom ≫ f' i = f i ≫ e.hom)
    (hsh : (Presieve.ofArrows W' f').IsSheafFor G) :
    (Presieve.ofArrows W f).IsSheafFor G := by
  have hd' : ∀ i, f' i ≫ e.inv = (d i).inv ≫ f i := by
    intro i
    rw [Iso.eq_inv_comp, ← Category.assoc, hd i, Category.assoc, e.hom_inv_id, Category.comp_id]
  intro x hx
  set y : ∀ i, G.obj (op (W i)) := fun i => x (f i) (Presieve.ofArrows.mk i) with hy
  have hcompat : ∀ (i j : κ) (A : C) (α : A ⟶ W' i) (β : A ⟶ W' j), α ≫ f' i = β ≫ f' j →
      G.map α.op (G.map (d i).inv.op (y i)) = G.map β.op (G.map (d j).inv.op (y j)) := by
    intro i j A α β hαβ
    rw [map_map_apply, map_map_apply]
    refine hx _ _ (Presieve.ofArrows.mk i) (Presieve.ofArrows.mk j) ?_
    rw [Category.assoc, Category.assoc, ← hd' i, ← hd' j, ← Category.assoc, ← Category.assoc,
      hαβ]
  obtain ⟨t', ht'⟩ := exists_section_of_isSheafFor_ofArrows W' f' hsh
    (fun i => G.map (d i).inv.op (y i)) hcompat
  have hrestr : ∀ i, G.map (f i).op (G.map e.hom.op t') = y i := by
    intro i
    rw [map_map_apply, ← hd i, ← map_map_apply, ht' i, map_map_apply, (d i).hom_inv_id,
      map_id_apply]
  refine ⟨G.map e.hom.op t', ?_, ?_⟩
  · rintro A h ⟨i⟩
    exact hrestr i
  · intro t₂ ht₂
    have hu : ∀ i, G.map (f' i).op (G.map e.inv.op t₂) = G.map (d i).inv.op (y i) := by
      intro i
      rw [map_map_apply, hd' i, ← map_map_apply, ht₂ (f i) (Presieve.ofArrows.mk i)]
    have heq : G.map e.inv.op t₂ = t' :=
      hsh.isSeparatedFor.ext (by rintro A g ⟨i⟩; rw [hu i, ht' i])
    rw [← heq, map_map_apply, e.hom_inv_id, map_id_apply]

/-- **The extension satisfies the sheaf condition for the `τ`-coverings of an object of the
subcategory by objects of the subcategory.** This is the sheaf condition for `F'` on `Sch/S`, not
for `F` on `𝒞`: the compatibility of a family of sections is tested on every object of `Sch/S`
mapping to two members of the covering, and the amalgamation is asked for in `F' X` rather than
in `F X`.

Both conditions pass across the identification of the restriction of `F'` to `𝒞` with `F`
(Stacks 0EUW), and in the easy direction: a family compatible on all of `Sch/S` is in particular
compatible on `𝒞`, where the `τ`-sheaf condition on `𝒞` amalgamates it, and the amalgamation is
transported back by the identification, which is bijective at each object of `𝒞`.

This is the sheaf condition of the extension at a *stage* of the presentation of an affine object
of `Sch/S` as a directed limit of objects of the subcategory; the hypothesis `hstd` of
`AlgebraicGeometry.ExtendingFunctors.isCoveringSheaf_extension_of_isCoveringSheafOnSubcategory`
asks for it at the limit, and what remains between the two is the interchange of the sheaf
condition with the filtered colimit. -/
theorem isSheafFor_extension_of_isCoveringSheafOnSubcategory (τ : CoveringTopology)
    (F : P.FullSubcategoryᵒᵖ ⥤ Type (max w (u + 1))) (hP1 : HasAffineOpens P)
    (hP2 : HasFinitePresentationAffines P) (haF : IsZariskiSheafOnSubcategory P F)
    (hbF : PreservesAffineLimitsOnSubcategory P F)
    (hF : IsCoveringSheafOnSubcategory.{max w (u + 1), u, v} τ P F)
    {ι : Type v} (V : P.FullSubcategory) (W : ι → P.FullSubcategory) (f : ∀ i, W i ⟶ V)
    (hcov : Presieve.ofArrows (fun i => (W i).obj) (fun i => P.ι.map (f i))
      ∈ coveringPrecoverage S τ V.obj) :
    (Presieve.ofArrows (fun i => (W i).obj) (fun i => P.ι.map (f i))).IsSheafFor
      (extension P F) := by
  classical
  obtain ⟨θ⟩ := nonempty_restrictionIso F hP1 hP2 haF hbF
  have hiso : ∀ Z : P.FullSubcategoryᵒᵖ, IsIso (θ.hom.app Z) :=
    fun Z => NatIso.isIso_app_of_isIso θ.hom Z
  have hbij : ∀ Z : P.FullSubcategoryᵒᵖ, Function.Bijective (θ.hom.app Z) := by
    intro Z
    rw [← isIso_iff_bijective]
    exact hiso Z
  have hsh := hF V W f hcov
  intro x hx
  set y : ∀ i, (extension P F).obj (op (W i).obj) :=
    fun i => x (P.ι.map (f i)) (Presieve.ofArrows.mk i) with hy
  have hcompat : ∀ (i j : ι) (A : P.FullSubcategory) (α : A ⟶ W i) (β : A ⟶ W j),
      α ≫ f i = β ≫ f j →
        F.map α.op (θ.hom.app (op (W i)) (y i)) = F.map β.op (θ.hom.app (op (W j)) (y j)) := by
    intro i j A α β hαβ
    rw [← natTrans_apply P.ι θ.hom α, ← natTrans_apply P.ι θ.hom β]
    refine congrArg (θ.hom.app (op A)) ?_
    refine hx (P.ι.map α) (P.ι.map β) (Presieve.ofArrows.mk i) (Presieve.ofArrows.mk j) ?_
    rw [← Functor.map_comp, ← Functor.map_comp, hαβ]
  obtain ⟨s, hs⟩ := exists_section_of_isSheafFor_ofArrows W f hsh
    (fun i => θ.hom.app (op (W i)) (y i)) hcompat
  obtain ⟨t, hts⟩ := (hbij (op V)).2 s
  have hti : ∀ i, (extension P F).map (P.ι.map (f i)).op t = y i := by
    intro i
    refine (hbij (op (W i))).1 ?_
    rw [natTrans_apply P.ι θ.hom (f i), hts, hs i]
  refine ⟨t, ?_, ?_⟩
  · rintro A h ⟨i⟩
    exact hti i
  · intro t₂ ht₂
    refine (hbij (op V)).1 (hsh.isSeparatedFor.ext ?_)
    rintro A g ⟨i⟩
    rw [← natTrans_apply P.ι θ.hom (f i), ← natTrans_apply P.ι θ.hom (f i)]
    exact congrArg (θ.hom.app (op (W i)))
      ((ht₂ (P.ι.map (f i)) (Presieve.ofArrows.mk i)).trans (hti i).symm)

/-- **The extension satisfies the sheaf condition for the `τ`-coverings of an object isomorphic
to an object of the subcategory by objects isomorphic to objects of the subcategory.** Conditions
(1) and (2) of Stacks 0EUW only place the affine opens of the objects of `𝒞` and the affine
schemes of finite presentation over the affine opens of `S` in `𝒞` *up to isomorphism*, so this
is the form in which
`AlgebraicGeometry.ExtendingFunctors.isSheafFor_extension_of_isCoveringSheafOnSubcategory` is
applied: a member of a covering produced by one of those conditions, or by a base change inside
`Sch/S`, is an object of `Sch/S` isomorphic to an object of `𝒞` rather than one of its objects. -/
theorem isSheafFor_extension_of_memUpToIso (τ : CoveringTopology)
    (F : P.FullSubcategoryᵒᵖ ⥤ Type (max w (u + 1))) (hP1 : HasAffineOpens P)
    (hP2 : HasFinitePresentationAffines P) (haF : IsZariskiSheafOnSubcategory P F)
    (hbF : PreservesAffineLimitsOnSubcategory P F)
    (hF : IsCoveringSheafOnSubcategory.{max w (u + 1), u, v} τ P F)
    {ι : Type v} {X : Over S} {W : ι → Over S} (f : ∀ i, W i ⟶ X)
    (hX : ∃ Y : Over S, P Y ∧ Nonempty (X ≅ Y))
    (hW : ∀ i, ∃ Y : Over S, P Y ∧ Nonempty (W i ≅ Y))
    (hcov : Presieve.ofArrows W f ∈ coveringPrecoverage S τ X) :
    (Presieve.ofArrows W f).IsSheafFor (extension P F) := by
  classical
  obtain ⟨Y, hY, ⟨e⟩⟩ := hX
  choose Z hZ hZiso using hW
  set dd : ∀ i, W i ≅ Z i := fun i => (hZiso i).some with hdd
  set V : P.FullSubcategory := ⟨Y, hY⟩ with hV
  set W' : ι → P.FullSubcategory := fun i => ⟨Z i, hZ i⟩ with hW'
  set f' : ∀ i, W' i ⟶ V := fun i =>
    ObjectProperty.homMk ((dd i).inv ≫ f i ≫ e.hom) with hf'
  have hdcomp : ∀ i, (dd i).hom ≫ P.ι.map (f' i) = f i ≫ e.hom := by
    intro i
    show (dd i).hom ≫ (dd i).inv ≫ f i ≫ e.hom = f i ≫ e.hom
    rw [Iso.hom_inv_id_assoc]
  refine isSheafFor_ofArrows_of_iso e dd f (fun i => P.ι.map (f' i)) hdcomp ?_
  exact isSheafFor_extension_of_isCoveringSheafOnSubcategory τ F hP1 hP2 haF hbF hF V W' f'
    (ofArrows_mem_coveringPrecoverage_of_iso τ e dd f (fun i => P.ι.map (f' i)) hdcomp hcov)

/-! ### A Zariski sheaf on `Sch/S` is a sheaf for every covering by open immersions -/

/-- The source of an open immersion of `Sch/S`, identified with the open subobject of the target
which is its image. -/
noncomputable def overOpenIso {A B : Over S} (g : A ⟶ B) [IsOpenImmersion g.left] :
    A ≅ overOpen B g.left.opensRange :=
  Over.isoMk g.left.isoOpensRange (by
    have h : g.left.isoOpensRange.hom ≫ g.left.opensRange.ι = g.left := by simp
    change g.left.isoOpensRange.hom ≫ g.left.opensRange.ι ≫ B.hom = A.hom
    rw [← Category.assoc, h, Over.w g])

/-- The inverse of `overOpenIso g` followed by `g` is the inclusion of the open subobject
`g.left.opensRange` into `B`. -/
@[simp]
lemma overOpenIso_inv_comp {A B : Over S} (g : A ⟶ B) [IsOpenImmersion g.left] :
    (overOpenIso g).inv ≫ g = overOpenι B g.left.opensRange := by
  refine Over.OverMorphism.ext ?_
  rw [Over.comp_left, overOpenι_left]
  have h : g.left.isoOpensRange.hom ≫ g.left.opensRange.ι = g.left := by simp
  have hinv : (overOpenIso g).inv.left = g.left.isoOpensRange.inv := by simp [overOpenIso]
  rw [hinv, Iso.inv_comp_eq]
  exact h.symm

/-- **A Zariski sheaf on `Sch/S` is a sheaf for every jointly surjective family of open
immersions.** The Zariski sheaf condition of
`AlgebraicGeometry.ExtendingFunctors.IsZariskiSheaf` is stated for a family of *opens* of the
target; a member of the given family is identified with the open subobject which is its image,
and choosing one member through each point of the target indexes the resulting open covering by
the points of the target, which is a type in the universe the condition asks for.

The glued section restricts correctly on each member of the family: the member is covered by the
inverse images of the chosen opens, over each of which the restriction of the glued section and
the given section are two restrictions of the compatible family along morphisms into two members
which agree over the target. -/
theorem isSheafFor_ofArrows_of_isZariskiSheaf {G : (Over S)ᵒᵖ ⥤ Type w}
    (haG : IsZariskiSheaf G) {X : Over S} {ι : Type v} (Yc : ι → Over S) (f : ∀ i, Yc i ⟶ X)
    (hfopen : ∀ i, IsOpenImmersion (f i).left)
    (hfcov : ⨆ i, (f i).left.opensRange = ⊤) :
    (Presieve.ofArrows Yc f).IsSheafFor G := by
  classical
  intro x hx
  have hxi : ∀ (i j : ι) (A : Over S) (α : A ⟶ Yc i) (β : A ⟶ Yc j), α ≫ f i = β ≫ f j →
      G.map α.op (x (f i) (Presieve.ofArrows.mk i))
        = G.map β.op (x (f j) (Presieve.ofArrows.mk j)) :=
    fun i j A α β h => hx α β (Presieve.ofArrows.mk i) (Presieve.ofArrows.mk j) h
  have hpt : ∀ z : X.left, ∃ i, z ∈ (f i).left.opensRange := by
    intro z
    have hz : z ∈ (⨆ i, (f i).left.opensRange) := by rw [hfcov]; trivial
    exact TopologicalSpace.Opens.mem_iSup.mp hz
  choose iz hiz using hpt
  have hVcov : ⨆ z : X.left, (f (iz z)).left.opensRange = ⊤ :=
    le_antisymm le_top fun z _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨z, hiz z⟩
  have he : ∀ i, (overOpenIso (f i)).inv ≫ f i = overOpenι X (f i).left.opensRange :=
    fun i => overOpenIso_inv_comp (f i)
  set s : ∀ z : X.left, G.obj (op (overOpen X (f (iz z)).left.opensRange)) :=
    fun z => G.map ((overOpenIso (f (iz z))).inv).op (x (f (iz z)) (Presieve.ofArrows.mk _))
    with hs
  obtain ⟨t, hts, htu⟩ := haG X X.left (fun z => (f (iz z)).left.opensRange) hVcov s (by
    intro z z'
    rw [hs, map_map_apply, map_map_apply]
    refine hxi _ _ _ _ _ ?_
    rw [Category.assoc, Category.assoc, he, he, overOpenLE_comp_overOpenι,
      overOpenLE_comp_overOpenι])
  refine ⟨t, ?_, ?_⟩
  · intro A hmor hh
    obtain ⟨i⟩ := hh
    refine zariskiSheaf_ext haG (fun z : X.left => (f i).left ⁻¹ᵁ (f (iz z)).left.opensRange)
      ?_ _ _ fun z => ?_
    · rw [← Scheme.Hom.preimage_iSup, hVcov, Scheme.Hom.preimage_top]
    · have hr : Set.range (⇑(overOpenι (Yc i) ((f i).left ⁻¹ᵁ (f (iz z)).left.opensRange)
          ≫ f i).left) ⊆ (((f (iz z)).left.opensRange : X.left.Opens) : Set X.left) := by
        rintro _ ⟨y, rfl⟩
        exact y.2
      have hlift := liftOverOpen_comp_overOpenι
        (overOpenι (Yc i) ((f i).left ⁻¹ᵁ (f (iz z)).left.opensRange) ≫ f i)
        (f (iz z)).left.opensRange hr
      rw [map_map_apply, ← hlift, ← map_map_apply, hts z, hs, map_map_apply]
      refine hxi _ _ _ _ _ ?_
      rw [Category.assoc, he, hlift]
  · intro t' ht'
    refine zariskiSheaf_ext haG (fun z : X.left => (f (iz z)).left.opensRange) hVcov t' t
      fun z => ?_
    rw [hts z, hs, ← he, ← map_map_apply, ht' (f (iz z)) (Presieve.ofArrows.mk _)]

/-- **A Zariski sheaf on `Sch/S` satisfies the sheaf condition for all Zariski coverings.** A
Zariski covering is exactly a jointly surjective family of open immersions. -/
theorem isCoveringSheaf_zariski_of_isZariskiSheaf {G : (Over S)ᵒᵖ ⥤ Type w}
    (haG : IsZariskiSheaf G) : IsCoveringSheaf.{w, u, v} .zariski G := by
  intro ι X Yc f hf
  obtain ⟨hsurj, hprop⟩ := (ofArrows_mem_coveringPrecoverage_iff .zariski Yc f).mp hf
  exact isSheafFor_ofArrows_of_isZariskiSheaf haG Yc f hprop
    (le_antisymm le_top fun z _ => TopologicalSpace.Opens.mem_iSup.mpr (hsurj z))

/-! ### The extension of a `τ`-sheaf -/

/-- **Stacks 0EUX for `τ = Zariski`.** Let `S` be a scheme, let `𝒞` be a full subcategory of
`Sch/S` satisfying conditions (1) and (2) of Stacks 0EUW — the big Zariski site `(Sch/S)_Zar` is
such a subcategory — and let `F : 𝒞ᵒᵖ ⥤ Set` be a Zariski sheaf on `𝒞`. Then the extension `F'`
of `F` to all schemes over `S` satisfies the sheaf condition for all Zariski coverings.

Property (b) of Stacks 0EUW, which the source assumes, is not needed for this clause: the
extension is a Zariski sheaf whatever `F` does to directed limits of affines, and a Zariski sheaf
is a sheaf for every Zariski covering. It is property (b) that makes
`AlgebraicGeometry.ExtendingFunctors.extension` deserve the name `F'`, by identifying its
restriction to `𝒞` with `F`; the conclusion below is about that same functor, assumed or not. -/
@[stacks 0EUX "τ = Zariski"]
theorem isCoveringSheaf_zariski_extension (P : ObjectProperty (Over S))
    (F : P.FullSubcategoryᵒᵖ ⥤ Type (max w (u + 1)))
    (hP1 : HasAffineOpens P) (hP2 : HasFinitePresentationAffines P)
    (hF : IsCoveringSheafOnSubcategory.{max w (u + 1), u, u} .zariski P F) :
    IsCoveringSheaf.{max w (u + 1), u, v} .zariski (extension P F) :=
  isCoveringSheaf_zariski_of_isZariskiSheaf (isZariskiSheaf_extension P F hP1 hP2
    (isZariskiSheafOnSubcategory_of_isCoveringSheafOnSubcategory .zariski hP1 hF))

/-- **The conclusion of Stacks 0EUX, from a hypothesis which is redundant but which this file
cannot discharge.** Let `τ` be one of Zariski, étale, smooth, syntomic and fppf, let `S` be a
scheme, let `𝒞` be a full subcategory of `Sch/S` satisfying conditions (1) and (2) of Stacks
0EUW — the big site `(Sch/S)_τ` is such a subcategory — and let `F : 𝒞ᵒᵖ ⥤ Set` be a `τ`-sheaf
on `𝒞` satisfying property (b) of Stacks 0EUW. Then the extension `F'` of `F` to all schemes over
`S` satisfies the sheaf condition for all `τ`-coverings.

Property (b) is what makes `AlgebraicGeometry.ExtendingFunctors.extension` deserve the name `F'`,
by identifying its restriction to `𝒞` with `F` (Stacks 0EUW); the deduction below does not use
it again.

The hypothesis `hstd` is the sheaf condition of the extension for the standard `τ`-coverings of
the affine objects of `Sch/S` lying over an affine open of `S`. **It is redundant**: it follows
from the other hypotheses by
`AlgebraicGeometry.ExtendingFunctors.isStandardAffineSheaf_extension`, which is proved in
`StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsStandardAffineInterchange`. That file
imports this one, so the discharge cannot be cited here, and that is the only reason the
conditional form is stated: it is what the unconditional statement of Stacks 0EUX,
`AlgebraicGeometry.ExtendingFunctors.isCoveringSheaf_extension_of_isCoveringSheafOnSubcategory'`
in that file, factors through. See the implementation notes of this file. For `τ = Zariski` the
hypothesis is superfluous outright, and
`AlgebraicGeometry.ExtendingFunctors.isCoveringSheaf_zariski_extension` is the resulting
unconditional statement. -/
theorem isCoveringSheaf_extension_of_isCoveringSheafOnSubcategory (τ : CoveringTopology)
    (P : ObjectProperty (Over S)) (F : P.FullSubcategoryᵒᵖ ⥤ Type (max w (u + 1)))
    (hP1 : HasAffineOpens P) (hP2 : HasFinitePresentationAffines P)
    (hF : IsCoveringSheafOnSubcategory.{max w (u + 1), u, u} τ P F)
    (_hbF : PreservesAffineLimitsOnSubcategory P F)
    (hstd : IsStandardAffineSheaf.{max w (u + 1), u, v} τ (extension P F)) :
    IsCoveringSheaf.{max w (u + 1), u, v} τ (extension P F) :=
  isCoveringSheaf_extension τ P F hP1 hP2
    (isZariskiSheafOnSubcategory_of_isCoveringSheafOnSubcategory τ hP1 hF) hstd

end AlgebraicGeometry.ExtendingFunctors

end
