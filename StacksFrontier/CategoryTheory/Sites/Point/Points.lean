module
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.MorphismDefs
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Topos.Sheaf
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

/-!
# A point of a site comes from a morphism of sites

Let `p` be a point of a site `(C, J)`, given by a fibre functor `u : C ⥤ Sets`. Let `𝒮` be a
site whose underlying category is a full subcategory `ι : S ⥤ Sets` of the category of sets,
whose coverings are the jointly surjective families, and which contains a singleton `e` and
every `u(U)`; the source builds one out of the powerset of an infinite set containing all the
`u(U)` (Stacks 00XD). Then

1. sheaves of sets on `𝒮` are the same thing as sets: taking sections over `e` is an
   equivalence `Sh(𝒮) → Sh(pt)`, quasi-inverse to `i_* : E ↦ (V ↦ Mor(V, E))`;
2. the fibre functor, read as a functor `u : C ⥤ 𝒮`, is continuous and defines a morphism of
   sites `f : 𝒮 → C` (Stacks 00X1); and
3. the composition `Sh(pt) → Sh(𝒮) → Sh(C)` is the morphism of topoi `(p_*, p⁻¹)` attached to
   the point `p` (Stacks 00YA): on pushforwards, `f_*i_*E(U) = i_*E(u(U)) = Mor(u(U), E)`,
   which is the skyscraper sheaf `p_*E` of Stacks 04EI.

So a point of a site is not merely a point of its topos but is induced by a morphism of sites,
after replacing `Sh(pt)` by the equivalent topos `Sh(𝒮)`.

## Main results

* `CategoryTheory.GrothendieckTopology.Point.exists_equivalence_isMorphismOfSites_pushforward_iso`:
  the lemma of Stacks 04EL.

## Implementation notes

* The site `𝒮`. The source cuts the class of all sets down to a set by choosing an infinite
  `S₀` with `u(U) ⊆ S₀` for all `U` and taking `S = 𝒫(S₀)`; the resulting category of sheaves
  does not depend on that choice, and the properties of `𝒮` its proofs use are that `𝒮` is a
  full subcategory `ι` of sets, that some object `e` of `𝒮` is a singleton, that every `u(U)` is
  an object of `𝒮`, and that a family of maps in `𝒮` is a covering exactly when it is jointly
  surjective. Those are the hypotheses below, so the statement is about every such site rather
  than about one choice of `S₀`, and the powerset of an infinite set containing all the `u(U)`
  is a witness. The singleton is the hypothesis under which the source proves clause (1); it
  also observes there that a nonempty object with an endomorphism of singleton image would do
  instead, and every powerset has singletons, so nothing about `04EL` is lost. Two of the
  source's requirements are absent: `S₀` need not be infinite,
  and `𝒮` need not have fibre products — a site in the source's sense (Stacks 00VS) must have
  the fibre products occurring in its coverings, whereas a Mathlib `GrothendieckTopology` is
  sieve-based and needs none, and (1), (2) and (3) use only fullness, faithfulness and the
  singleton. The site of *all* sets is not an instance of the statement (`Type w` is not
  `Type w`-small); for it, clause (1) is Mathlib's `CategoryTheory.typeEquiv` and
  `CategoryTheory.typesGrothendieckTopology`.
* "`u(U) ⊆ S₀` for all `U`", i.e. that the fibre functor factors through `𝒮`, is the datum of a
  functor `u : C ⥤ S` together with an isomorphism `u ⋙ ι ≅ Φ.fiber`; an isomorphism rather
  than an equality, since nothing in the mathematics distinguishes `u(U)` from a set isomorphic
  to it.
* A point of the site is Mathlib's `GrothendieckTopology.Point`, i.e. a fibre functor in the
  sense of SGA 4 IV 6.3: conditions (1) and (2) of Stacks 00Y5 are its `jointly_surjective`
  field and the cofilteredness of its category of elements, and condition (3) — exactness of
  the stalk functor — is then a theorem (`Point.sheafFiber_leftExact`) rather than an
  assumption. Its morphism of topoi `(p_*, p⁻¹)` of Stacks 00YA is
  `(Φ.skyscraperSheafFunctor, Φ.sheafFiber)`.
* Local `w`-smallness of `C`, i.e. that every `Hom(X, Y)` is in bijection with a set in
  `Type w`, is what makes that theorem available, and it is a hypothesis of `04EL` rather than
  a convenience. The stalk functor is the colimit of the sections of `F` over the category of
  elements of `u`, whose objects form a `max u w`-sized and whose morphisms a `v`-sized family;
  such a colimit computes and is exact in `Type w` once the shape is `w`-small up to a final
  subcategory, and local `w`-smallness of `C` is what provides that. It is therefore what makes
  clause (2) *true*: given (1) and (3), the left adjoint clause (2) asks for is `Φ.sheafFiber`
  transported along `i`, so clause (2)'s left-exactness half is `Point.sheafFiber_leftExact`
  (Stacks 00Y5 (3)), and clause (3)'s reading as "the morphism of topoi of Stacks 00YA" is the
  existence of `Point.pointOfTopos`, which needs the same hypothesis. Nothing of the source is
  lost: a site there has a small underlying category, and `Category.{w} C` on `C : Type w` gives
  local `w`-smallness by `CategoryTheory.locallySmall_self`, as does `UnivLE.{v, w}` in general.
* Clause (1) is stated with the equivalence pinned on its inverse-image side, as taking
  sections over the singleton `e`, which is how Mathlib states the same equivalence for the
  site of all sets (`CategoryTheory.typeEquiv`) and is the functor `i⁻¹` of the source's
  equation (05UW). This determines `i_*` up to isomorphism, and determines it to be the source's
  `E ↦ (V ↦ Mor(V, E))`: a sheaf `F` on `𝒮` satisfies `F(V) ≅ Mor(ι V, F(e))`, because the maps
  `e → V` picking out the points of `ι V` form a covering.
* Clause (2) is `IsMorphismOfSites.{w}` of Stacks 00X1 (the universe-general class in
  `StacksFrontier/CategoryTheory/Sites/MorphismOfSites/MorphismDefs.lean`): it extends
  `u.IsContinuous J K` — which is why "is continuous" is not a separate conjunct — and asks
  that `u^s = u.sheafPushforwardContinuous` admit a left exact left adjoint `u_s`, the
  right-exactness half of Stacks 00X1 being automatic for a left adjoint. It is bound by the
  existential so that `u^s` elaborates in clause (3), as in Stacks 03A2.
* Clause (3) is an isomorphism of pushforward functors, i.e. an invertible 2-morphism of
  morphisms of topoi (Stacks 04IA); by uniqueness of left adjoints it transports to an
  isomorphism of the inverse images, and it is the side on which the source's proof computes.
  The source's `i_*` and `f_*` are `e.functor` and `u.sheafPushforwardContinuous`, and the
  latter is by construction restriction along `u.op`, so the composite is
  `E ↦ (U ↦ Mor(ι (u U), E))` and the clause says exactly that this is the skyscraper sheaf.

Faithfulness. (1) No hypothesis is dead: `Φ` and `u` are tied together by `hu` and both occur
in the conclusion, the fullness and faithfulness of `ι`, the singleton `pt` and the description
`hK` of `K` are what make (1) true, `J` and `K` occur in both remaining clauses, and local
`w`-smallness of `C` is what makes (2) true and (3) expressible. (2) The base is the source's:
`Sh(pt)` is the category of sets in the guise of `Type w`, `𝒮` is a full
subcategory of sets, and all sheaves are sheaves of sets, on the given `(C, J)` and `(S, K)`.
(3) The canonical maps are pinned: (1) is not the bare existence of an equivalence but names its
inverse image, and (3) is an isomorphism with the skyscraper functor `p_*` of the given point
itself, not with some functor. (4) The instantiation is not degenerate: `S = 𝒫(S₀)` for an
infinite `S₀` receiving all the `u(U)` satisfies the hypotheses with `ι` the inclusion and `pt`
a singleton subset — such an `S₀` in `Type w` exists exactly when `Σ U, u(U)` does, i.e. when
`u ≤ w`, which is the case for the small site of the source — and points of a locally `w`-small
site exist, e.g. `GrothendieckTopology.pointBot X` for the discrete topology, whose fibre
functor is `Hom(X, -)`.

## References

* [Stacks 04EL](https://stacks.math.columbia.edu/tag/04EL)
  (`sites-lemma-point-morphism-sites`), in the section "Points". The site built from a
  powerset and clause (1) are Stacks 00XD, points of a site are Stacks 00Y5, the morphism of
  topoi of a point is Stacks 00YA, morphisms of sites are Stacks 00X1, and the formula
  `p_*E(U) = Mor(u(U), E)` is Stacks 04EI.
-/

section

universe w v u t
open CategoryTheory Limits
open CategoryTheory Limits Opposite

namespace Stacks.SitePoints.MorphismOfSites

private lemma pi_element_ext {I : Type w} {f : I → Type w} {x y : (∏ᶜ f : Type w)}
    (h : ∀ i, Pi.π f i x = Pi.π f i y) : x = y :=
  Limits.Types.limit_ext _ x y (fun ⟨i⟩ ↦ h i)

private lemma isIso_pi_π_of_unique {I : Type w} [Unique I] (E : Type w) :
    IsIso (Pi.π (fun _ : I ↦ E) default) := by
  refine ⟨⟨Pi.lift (fun _ ↦ 𝟙 E), Pi.hom_ext _ _ fun i ↦ ?_, ?_⟩⟩
  · rw [Category.assoc, Pi.lift_comp_π, Category.comp_id, Category.id_comp,
      Subsingleton.elim i (default : I)]
  · rw [Pi.lift_comp_π]

/-! ### The punctual object of a full subcategory of sets -/

section Punctual

variable {S : Type w} [SmallCategory S] (ι : S ⥤ Type w) [hιfull : ι.Full] [hιfaith : ι.Faithful]
  (pt : S) [hptu : Unique (ι.obj pt)]

include ι hιfull hιfaith hptu

omit hιfull in
private lemma hom_pt_ext {V : S} (f g : V ⟶ pt) : f = g :=
  ι.map_injective (ConcreteCategory.hom_ext _ _ fun _ ↦ Subsingleton.elim _ _)

/-- The unique morphism from `V` to the singleton object `pt`. -/
private noncomputable def toPt (V : S) : V ⟶ pt :=
  ι.preimage (TypeCat.ofHom fun _ ↦ default)

/-- The morphism `pt ⟶ V` whose image is the point `x` of `ι V`. -/
private noncomputable def ptHom {V : S} (x : ι.obj V) : pt ⟶ V :=
  ι.preimage (TypeCat.ofHom fun _ ↦ x)

omit hιfaith hptu in
private lemma map_ptHom {V : S} (x : ι.obj V) (z : ι.obj pt) : ι.map (ptHom ι pt x) z = x := by
  have h : ι.map (ptHom ι pt x) = TypeCat.ofHom fun _ ↦ x := ι.map_preimage _
  rw [h]
  rfl

private lemma comp_toPt {W V : S} (h : W ⟶ V) : h ≫ toPt ι pt V = toPt ι pt W :=
  hom_pt_ext ι pt _ _

private lemma toPt_pt : toPt ι pt pt = 𝟙 pt :=
  hom_pt_ext ι pt _ _

private lemma ptHom_pt (x : ι.obj pt) : ptHom ι pt x = 𝟙 pt :=
  hom_pt_ext ι pt _ _

omit hptu in
private lemma ptHom_comp {V W : S} (x : ι.obj V) (g : V ⟶ W) :
    ptHom ι pt x ≫ g = ptHom ι pt (ι.map g x) :=
  ι.map_injective
    (ConcreteCategory.hom_ext _ _ fun z ↦ by
      rw [Functor.map_comp, types_comp_apply, map_ptHom, map_ptHom])

omit hptu in
/-- Restricting a section of `P` to `pt` along `ptHom x` and applying `α` is compatible with the
morphisms of the category of elements of `ι`: this is the cocone condition that defines
`toSky`. -/
private lemma map_ptHom_op_w {P : Sᵒᵖ ⥤ Type t} {E : Type t} (α : P.obj (op pt) ⟶ E) {X Y : S}
    (f : X ⟶ Y) (x : ι.obj X) :
    P.map f.op ≫ P.map (ptHom ι pt x).op ≫ α = P.map (ptHom ι pt (ι.map f x)).op ≫ α := by
  rw [← Category.assoc, ← Functor.map_comp, ← op_comp, ptHom_comp]

/-- The sieve on `V` generated by the morphisms `pt ⟶ V`. -/
private def covSieve (V : S) : Sieve V where
  arrows W g := ∃ x : ι.obj V, g = toPt ι pt W ≫ ptHom ι pt x
  downward_closed := by
    rintro W W' g ⟨x, rfl⟩ h
    exact ⟨x, by rw [← Category.assoc, comp_toPt]⟩

private lemma covSieve_ptHom {V : S} (x : ι.obj V) : (covSieve ι pt V).arrows (ptHom ι pt x) :=
  ⟨x, by rw [toPt_pt, Category.id_comp]⟩

/-- The category of elements of a full subcategory of sets containing a singleton has an
initial object. -/
private noncomputable def elementsInitial : IsInitial (ι.elementsMk pt (default : ι.obj pt)) := by
  refine
    IsInitial.ofUniqueHom (fun V ↦ ⟨ptHom ι pt V.2, map_ptHom ι pt V.2 default⟩) (fun V m ↦ ?_)
  refine Functor.Elements.hom_ext ?_
  dsimp only
  refine ι.map_injective (ConcreteCategory.hom_ext _ _ fun z ↦ ?_)
  rw [map_ptHom, Subsingleton.elim z (default : ι.obj pt)]
  exact m.2

end Punctual

/-! ### The fibre functor of a point, read through `hu` -/

section Fibre

variable {S : Type w} [SmallCategory S] (ι : S ⥤ Type w) [hιfull : ι.Full] [hιfaith : ι.Faithful]
  (pt : S) [hptu : Unique (ι.obj pt)] {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (Φ : GrothendieckTopology.Point.{w} J) (u : C ⥤ S) (hu : u ⋙ ι ≅ Φ.fiber)

/-- Two elements of the fibres of `Φ.fiber` with the same image over `Z` are dominated by a
single element: the elementwise form of the cofilteredness of the category of elements of
`Φ.fiber`. -/
private lemma exists_cospan_of_map_eq {Y₁ Y₂ Z : C} (g₁ : Y₁ ⟶ Z) (g₂ : Y₂ ⟶ Z)
    {a₁ : Φ.fiber.obj Y₁} {a₂ : Φ.fiber.obj Y₂} (ha : Φ.fiber.map g₁ a₁ = Φ.fiber.map g₂ a₂) :
    ∃ (W : C) (c : Φ.fiber.obj W) (h₁ : W ⟶ Y₁) (h₂ : W ⟶ Y₂),
      h₁ ≫ g₁ = h₂ ≫ g₂ ∧ Φ.fiber.map h₁ c = a₁ ∧ Φ.fiber.map h₂ c = a₂ := by
  let α₁ : Φ.fiber.elementsMk Y₁ a₁ ⟶ Φ.fiber.elementsMk Z (Φ.fiber.map g₁ a₁) := ⟨g₁, rfl⟩
  let α₂ : Φ.fiber.elementsMk Y₂ a₂ ⟶ Φ.fiber.elementsMk Z (Φ.fiber.map g₁ a₁) := ⟨g₂, ha.symm⟩
  obtain ⟨z, q₁, q₂, fac⟩ := IsCofiltered.cospan α₁ α₂
  replace fac := congrArg Functor.Elements.Hom.hom fac
  exact ⟨z.1, z.2, q₁.1, q₂.1, fac, q₁.map_val, q₂.map_val⟩

omit hιfull hιfaith in
/-- `hu` read on elements: it takes `ι (u g)` to `Φ.fiber g`. -/
private lemma hu_hom_map {X Y : C} (g : X ⟶ Y) (b : ι.obj (u.obj X)) :
    hu.hom.app Y (ι.map (u.map g) b) = Φ.fiber.map g (hu.hom.app X b) := by
  simpa only [types_comp_apply, Functor.comp_map, Functor.comp_obj] using
    ConcreteCategory.congr_hom (hu.hom.naturality g) b

omit hιfull hιfaith in
/-- `hu` read backwards on elements: an element of `Φ.fiber X` whose image under `h` is the one
`hu` attaches to `b` is carried to `b` by `ι (u h)`. -/
private lemma map_map_hu_inv {X Y : C} (h : X ⟶ Y) (c : Φ.fiber.obj X) (b : ι.obj (u.obj Y))
    (hb : Φ.fiber.map h c = hu.hom.app Y b) : ι.map (u.map h) (hu.inv.app X c) = b := by
  have n := ConcreteCategory.congr_hom (hu.inv.naturality h) c
  have m := ConcreteCategory.congr_hom (hu.hom_inv_id_app Y) b
  simp only [types_comp_apply, types_id_apply, Functor.comp_map, Functor.comp_obj] at n m
  rw [← n, hb, m]

include hιfull hιfaith hptu in
omit hptu in
/-- The same statement at the level of the morphisms out of `pt`: the point of `u X` cut out by
`c` becomes, after `u h`, the point of `u Y` cut out by `b`. -/
private lemma ptHom_hu_inv_comp {X Y : C} (h : X ⟶ Y) (c : Φ.fiber.obj X) (b : ι.obj (u.obj Y))
    (hb : Φ.fiber.map h c = hu.hom.app Y b) :
    ptHom ι pt (hu.inv.app X c) ≫ u.map h = ptHom ι pt b := by
  rw [ptHom_comp, map_map_hu_inv ι Φ u hu h c b hb]

end Fibre

/-! ### The point of the site `(S, K)` and the equivalence with sets -/

section Topology

variable {S : Type w} [SmallCategory S] (ι : S ⥤ Type w) [hιfull : ι.Full] [hιfaith : ι.Faithful]
  (pt : S) [hptu : Unique (ι.obj pt)] (K : GrothendieckTopology S)
  (hK :
    ∀ (V : S) (R : Sieve V),
      R ∈ K V ↔ ∀ x : ι.obj V, ∃ (W : S) (f : W ⟶ V) (y : ι.obj W), R.arrows f ∧ ι.map f y = x)

include ι hιfull hιfaith hptu hK

private lemma covSieve_mem (V : S) : covSieve ι pt V ∈ K V := by
  rw [hK]
  intro x
  exact ⟨pt, ptHom ι pt x, default, covSieve_ptHom ι pt x, map_ptHom ι pt x default⟩

/-- Two sections of a `K`-sheaf are equal if they agree after restriction along every
`ptHom x`. -/
private lemma sheaf_ext_of_ptHom (F : Sheaf K (Type t)) {V : S} {s₁ s₂ : F.obj.obj (op V)}
    (h : ∀ x : ι.obj V, F.obj.map (ptHom ι pt x).op s₁ = F.obj.map (ptHom ι pt x).op s₂) :
    s₁ = s₂ := by
  refine (((isSheaf_iff_isSheaf_of_type K F.obj).1 F.property).isSeparated (covSieve ι pt V)
    (covSieve_mem ι pt K hK V)).ext ?_
  rintro W g ⟨x, rfl⟩
  rw [op_comp, Functor.map_comp, types_comp_apply, types_comp_apply, h x]

/-- The fibre functor `ι` makes `(S, K)` into a pointed site. -/
private noncomputable def pointOfSite : GrothendieckTopology.Point.{w} K where
  fiber := ι
  isCofiltered := IsCofiltered.of_isInitial _ (elementsInitial ι pt)
  initiallySmall :=
    haveI : HasInitial ι.Elements := (elementsInitial ι pt).hasInitial
    inferInstance
  jointly_surjective R hR x := by
    obtain ⟨W, f, y, hf, hy⟩ := (hK _ R).1 hR x
    exact ⟨W, f, hf, y, hy⟩

private lemma sky_map_π (E : Type w) {V W : Sᵒᵖ} (φ : V ⟶ W) (y : ι.obj W.unop) :
    ((pointOfSite ι pt K hK).skyscraperPresheaf E).map φ ≫ Pi.π (fun _ : ι.obj W.unop ↦ E) y =
      Pi.π (fun _ : ι.obj V.unop ↦ E) (ι.map φ.unop y) := by
  have h :=
    Pi.map'_comp_π (f := fun _ : ι.obj V.unop ↦ E) (g := fun _ : ι.obj W.unop ↦ E)
      (fun z ↦ ι.map φ.unop z) (fun _ ↦ 𝟙 E) y
  rw [Category.comp_id] at h
  exact h

private lemma sky_map_op_apply_π {E : Type w} {V W : S} (f : W ⟶ V) (y : ι.obj W)
    (s : ((pointOfSite ι pt K hK).skyscraperPresheaf E).obj (op V)) :
    Pi.π (fun _ : ι.obj W ↦ E) y (((pointOfSite ι pt K hK).skyscraperPresheaf E).map f.op s) =
      Pi.π (fun _ : ι.obj V ↦ E) (ι.map f y) s :=
  ConcreteCategory.congr_hom (sky_map_π ι pt K hK E f.op y) s

private lemma sky_map_app_apply_π {E E' : Type w} (α : E ⟶ E') (V : Sᵒᵖ) (y : ι.obj V.unop)
    (s : ((pointOfSite ι pt K hK).skyscraperPresheaf E).obj V) :
    Pi.π (fun _ : ι.obj V.unop ↦ E') y
        (((pointOfSite ι pt K hK).skyscraperPresheafFunctor.map α).app V s) =
      α (Pi.π (fun _ : ι.obj V.unop ↦ E) y s) :=
  ConcreteCategory.congr_hom
    (Pi.map_π (f := fun _ : ι.obj V.unop ↦ E) (g := fun _ : ι.obj V.unop ↦ E') (fun _ ↦ α) y) s

/-- The morphism from a presheaf to the skyscraper presheaf induced by a map on the sections
over `pt`: the adjunction bijection of `Point.skyscraperPresheafHomEquiv` at the map out of the
fibre given by the initial object `(pt, ∗)` of the category of elements. -/
private noncomputable def toSky (P : Sᵒᵖ ⥤ Type w) {E : Type w} (α : P.obj (op pt) ⟶ E) :
    P ⟶ (pointOfSite ι pt K hK).skyscraperPresheaf E :=
  (pointOfSite ι pt K hK).skyscraperPresheafHomEquiv
    ((pointOfSite ι pt K hK).presheafFiberDesc (fun _V x ↦ P.map (ptHom ι pt x).op ≫ α)
      (fun _X _Y f x ↦ map_ptHom_op_w ι pt α f x))

private lemma toSky_app_comp_π (P : Sᵒᵖ ⥤ Type w) {E : Type w} (α : P.obj (op pt) ⟶ E) (V : Sᵒᵖ)
    (x : ι.obj V.unop) :
    (toSky ι pt K hK P α).app V ≫ Pi.π (fun _ : ι.obj V.unop ↦ E) x =
      P.map (ptHom ι pt x).op ≫ α :=
  ((pointOfSite ι pt K hK).skyscraperPresheafHomEquiv_app_π _ V.unop x).trans
    ((pointOfSite ι pt K hK).toPresheafFiber_presheafFiberDesc _ _ V.unop x)

private lemma toSky_app_π (P : Sᵒᵖ ⥤ Type w) {E : Type w} (α : P.obj (op pt) ⟶ E) (V : Sᵒᵖ)
    (x : ι.obj V.unop) (s : P.obj V) :
    Pi.π (fun _ : ι.obj V.unop ↦ E) x ((toSky ι pt K hK P α).app V s) =
      α (P.map (ptHom ι pt x).op s) :=
  ConcreteCategory.congr_hom (toSky_app_comp_π ι pt K hK P α V x) s

/-- Evaluating `toSky P α` at `pt` recovers `α`. -/
private lemma toSky_app_pt_π (P : Sᵒᵖ ⥤ Type w) {E : Type w} (α : P.obj (op pt) ⟶ E) :
    (toSky ι pt K hK P α).app (op pt) ≫ Pi.π (fun _ : ι.obj pt ↦ E) default = α := by
  refine ConcreteCategory.hom_ext _ _ fun s ↦ ?_
  refine (toSky_app_π ι pt K hK P α (op pt) default s).trans ?_
  simp [ptHom_pt]

/-- Conversely, every morphism `β` to a skyscraper presheaf is the morphism induced by the map
`β` defines on the sections over `pt`: a morphism to a skyscraper presheaf is determined by
that single map. This is the uniqueness half of `skyAdjunction`, and it uses no sheaf
condition. -/
private lemma toSky_app_pt_π_self (P : Sᵒᵖ ⥤ Type w) {E : Type w}
    (β : P ⟶ (pointOfSite ι pt K hK).skyscraperPresheaf E) :
    toSky ι pt K hK P (β.app (op pt) ≫ Pi.π (fun _ : ι.obj pt ↦ E) default) = β := by
  refine NatTrans.ext (funext fun V ↦ ?_)
  refine ConcreteCategory.hom_ext _ _ fun s ↦ ?_
  refine pi_element_ext (f := fun _ : ι.obj V.unop ↦ E) fun y ↦ ?_
  refine (toSky_app_π ι pt K hK P _ V y s).trans ?_
  change
    Pi.π (fun _ : ι.obj pt ↦ E) default (β.app (op pt) (P.map (ptHom ι pt y).op s)) =
      Pi.π (fun _ : ι.obj V.unop ↦ E) y (β.app V s)
  rw [NatTrans.naturality_apply,
    sky_map_op_apply_π ι pt K hK (ptHom ι pt y) (default : ι.obj pt) (β.app V s),
    map_ptHom ι pt y default]

private lemma toSky_comp_map (P : Sᵒᵖ ⥤ Type w) {E E' : Type w} (α : P.obj (op pt) ⟶ E)
    (g : E ⟶ E') :
    toSky ι pt K hK P (α ≫ g) =
      toSky ι pt K hK P α ≫ (pointOfSite ι pt K hK).skyscraperPresheafFunctor.map g := by
  refine NatTrans.ext (funext fun V ↦ ?_)
  refine ConcreteCategory.hom_ext _ _ fun s ↦ ?_
  refine pi_element_ext (f := fun _ : ι.obj V.unop ↦ E') fun y ↦ ?_
  refine (toSky_app_π ι pt K hK P (α ≫ g) V y s).trans ?_
  change
    g (α (P.map (ptHom ι pt y).op s)) =
      Pi.π (fun _ : ι.obj V.unop ↦ E') y
        (((pointOfSite ι pt K hK).skyscraperPresheafFunctor.map g).app V
          ((toSky ι pt K hK P α).app V s))
  rw [sky_map_app_apply_π, toSky_app_π]

/-- The adjunction between evaluation at `pt` and the skyscraper sheaf functor. -/
private noncomputable def skyAdjunction :
    sheafToPresheaf K (Type w) ⋙ (evaluation Sᵒᵖ (Type w)).obj (op pt) ⊣
      (pointOfSite ι pt K hK).skyscraperSheafFunctor (A := Type w) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun F E ↦
        { toFun := fun α ↦ ObjectProperty.homMk (toSky ι pt K hK F.obj α)
          invFun := fun β ↦ β.hom.app (op pt) ≫ Pi.π (fun _ : ι.obj pt ↦ E) default
          left_inv := fun α ↦ toSky_app_pt_π ι pt K hK F.obj α
          right_inv := fun β ↦ Sheaf.hom_ext (toSky_app_pt_π_self ι pt K hK F.obj β.hom) }
      homEquiv_naturality_left_symm := fun {F₁ F₂ E} f g ↦ by
        change
          (f.hom.app (op pt) ≫ g.hom.app (op pt)) ≫ Pi.π (fun _ : ι.obj pt ↦ E) default =
            f.hom.app (op pt) ≫ g.hom.app (op pt) ≫ Pi.π (fun _ : ι.obj pt ↦ E) default
        exact Category.assoc _ _ _
      homEquiv_naturality_right := fun {F E E'} f g ↦
        Sheaf.hom_ext (toSky_comp_map ι pt K hK F.obj f g) }

private lemma toSky_injective (F : Sheaf K (Type w)) (V : S) :
    Function.Injective ((toSky ι pt K hK F.obj (𝟙 (F.obj.obj (op pt)))).app (op V)) := by
  intro s₁ s₂ h
  refine sheaf_ext_of_ptHom ι pt K hK F fun x ↦ ?_
  have h2 := congrArg (Pi.π (fun _ : ι.obj V ↦ F.obj.obj (op pt)) x) h
  rw [toSky_app_π, toSky_app_π] at h2
  exact h2

private lemma imageSieve_toSky_mem (F : Sheaf K (Type w)) (V : S)
    (u : ((pointOfSite ι pt K hK).skyscraperPresheaf (F.obj.obj (op pt))).obj (op V)) :
    Presheaf.imageSieve (toSky ι pt K hK F.obj (𝟙 (F.obj.obj (op pt)))) u ∈ K V := by
  rw [hK]
  intro x
  refine
    ⟨pt, ptHom ι pt x, default, ⟨Pi.π (fun _ : ι.obj V ↦ F.obj.obj (op pt)) x u, ?_⟩,
      map_ptHom ι pt x default⟩
  refine pi_element_ext (f := fun _ : ι.obj pt ↦ F.obj.obj (op pt)) fun z ↦ ?_
  rw [toSky_app_π, sky_map_op_apply_π ι pt K hK (ptHom ι pt x) z u, map_ptHom, ptHom_pt, op_id,
    F.obj.map_id]
  rfl

private lemma toSky_surjective (F : Sheaf K (Type w)) (V : S) :
    Function.Surjective ((toSky ι pt K hK F.obj (𝟙 (F.obj.obj (op pt)))).app (op V)) := by
  intro u
  have hF : Presieve.IsSheaf K F.obj := (isSheaf_iff_isSheaf_of_type K F.obj).1 F.property
  have hT : Presieve.IsSheaf K ((pointOfSite ι pt K hK).skyscraperPresheaf (F.obj.obj (op pt))) :=
    (isSheaf_iff_isSheaf_of_type K _).1 ((pointOfSite ι pt K hK).isSheaf_skyscraperPresheaf _)
  have hR := imageSieve_toSky_mem ι pt K hK F V u
  set η := toSky ι pt K hK F.obj (𝟙 (F.obj.obj (op pt)))
  set x : Presieve.FamilyOfElements F.obj (Presheaf.imageSieve η u).arrows := fun _ g hg ↦
    Presheaf.localPreimage η u g hg with hx
  have hxc : x.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ hcomm
    refine toSky_injective ι pt K hK F Z ?_
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hx]
    rw [Presheaf.app_localPreimage, Presheaf.app_localPreimage, ← Functor.map_comp_apply, ←
      Functor.map_comp_apply, ← op_comp, ← op_comp, hcomm]
  refine ⟨(hF _ hR).amalgamate x hxc, ?_⟩
  refine (hT.isSeparated (Presheaf.imageSieve η u) hR).ext ?_
  intro W g hg
  rw [← NatTrans.naturality_apply, (hF _ hR).valid_glue hxc g hg, hx]
  exact Presheaf.app_localPreimage η u g hg

private lemma isIso_skyAdjunction_unit_app (F : Sheaf K (Type w)) :
    IsIso ((skyAdjunction ι pt K hK).unit.app F) := by
  have : ∀ V : Sᵒᵖ, IsIso ((toSky ι pt K hK F.obj (𝟙 (F.obj.obj (op pt)))).app V) := fun V ↦ by
    rw [isIso_iff_bijective]
    exact ⟨toSky_injective ι pt K hK F V.unop, toSky_surjective ι pt K hK F V.unop⟩
  have : IsIso ((sheafToPresheaf K (Type w)).map ((skyAdjunction ι pt K hK).unit.app F)) :=
    NatIso.isIso_of_isIso_app (toSky ι pt K hK F.obj (𝟙 (F.obj.obj (op pt))))
  exact isIso_of_reflects_iso _ (sheafToPresheaf K (Type w))

private lemma isIso_skyAdjunction_counit_app (E : Type w) :
    IsIso ((skyAdjunction ι pt K hK).counit.app E) := by
  have h : (skyAdjunction ι pt K hK).counit.app E = 𝟙 _ ≫ Pi.π (fun _ : ι.obj pt ↦ E) default :=
    rfl
  rw [h, Category.id_comp]
  exact isIso_pi_π_of_unique (I := ι.obj pt) E

/-- The equivalence between sets and `K`-sheaves of sets, with evaluation at `pt` as its
inverse image. -/
private noncomputable def setEquiv : Type w ≌ Sheaf K (Type w) :=
  haveI : ∀ F, IsIso ((skyAdjunction ι pt K hK).unit.app F) :=
    isIso_skyAdjunction_unit_app ι pt K hK
  haveI : ∀ E, IsIso ((skyAdjunction ι pt K hK).counit.app E) :=
    isIso_skyAdjunction_counit_app ι pt K hK
  ((skyAdjunction ι pt K hK).toEquivalence).symm

private lemma setEquiv_inverse :
    (setEquiv ι pt K hK).inverse =
      sheafToPresheaf K (Type w) ⋙ (evaluation Sᵒᵖ (Type w)).obj (op pt) :=
  rfl

private lemma setEquiv_functor :
    (setEquiv ι pt K hK).functor = (pointOfSite ι pt K hK).skyscraperSheafFunctor (A := Type w) :=
  rfl

/-! ### Continuity of the fibre functor -/

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (Φ : GrothendieckTopology.Point.{w} J) (u : C ⥤ S) (hu : u ⋙ ι ≅ Φ.fiber)

include Φ hu

omit hptu in
omit hιfull hιfaith in
private lemma coverPreserving : CoverPreserving J K u := by
  constructor
  intro U R hR
  rw [hK]
  intro z
  obtain ⟨Y, g, hg, y, hy⟩ := Φ.jointly_surjective R hR (hu.hom.app U z)
  exact
    ⟨u.obj Y, u.map g, hu.inv.app Y y, Presieve.image_mem_functorPushforward u R.arrows hg,
      map_map_hu_inv ι Φ u hu g y z hy⟩

private lemma compatiblePreserving : CompatiblePreserving.{t} K u := by
  constructor
  intro ℱ Z T x hx Y₁ Y₂ X f₁ f₂ g₁ g₂ hg₁ hg₂ he
  refine sheaf_ext_of_ptHom ι pt K hK ℱ fun a ↦ ?_
  have key :
    ℱ.obj.map (ptHom ι pt (ι.map f₁ a)).op (x g₁ hg₁) =
      ℱ.obj.map (ptHom ι pt (ι.map f₂ a)).op (x g₂ hg₂) := by
    have hcomm :
      Φ.fiber.map g₁ (hu.hom.app Y₁ (ι.map f₁ a)) =
        Φ.fiber.map g₂ (hu.hom.app Y₂ (ι.map f₂ a)) := by
      rw [← hu_hom_map, ← hu_hom_map, ← Functor.map_comp_apply, ← Functor.map_comp_apply, he]
    obtain ⟨W₀, c, h₁, h₂, hfac, hc₁, hc₂⟩ := exists_cospan_of_map_eq Φ g₁ g₂ hcomm
    have hxc := hx h₁ h₂ hg₁ hg₂ hfac
    simp only [Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op] at hxc
    rw [← ptHom_hu_inv_comp ι pt Φ u hu h₁ c _ hc₁, ← ptHom_hu_inv_comp ι pt Φ u hu h₂ c _ hc₂,
      op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, hxc]
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, ptHom_comp,
    ptHom_comp, key]

private lemma isContinuous : u.IsContinuous J K :=
  Functor.isContinuous_of_coverPreserving (compatiblePreserving ι pt K hK Φ u hu)
    (coverPreserving ι K hK Φ u hu)

/-- The pushforward along `u` of the skyscraper sheaf on `(S, K)` is the skyscraper sheaf of
the point `Φ`. -/
private noncomputable def pushforwardSkyscraperIso :
    haveI := isContinuous ι pt K hK Φ u hu
    (pointOfSite ι pt K hK).skyscraperSheafFunctor (A := Type w) ⋙
        u.sheafPushforwardContinuous (Type w) J K ≅
      Φ.skyscraperSheafFunctor (A := Type w) :=
  haveI := isContinuous ι pt K hK Φ u hu
  Functor.fullyFaithfulCancelRight (sheafToPresheaf J (Type w))
    (((flipFunctor Cᵒᵖ (Type w) (Type w)).mapIso
        (Functor.isoWhiskerRight (NatIso.op hu) (piFunctor.{w} (C := Type w)).flip)).symm)

end

end Topology

end Stacks.SitePoints.MorphismOfSites

namespace CategoryTheory.GrothendieckTopology.Point

@[expose] public section

open Stacks.SitePoints.MorphismOfSites in
/-- **Stacks 04EL.** Let `Φ` be a point of a locally `w`-small site `(C, J)`, with fibre functor
`u = Φ.fiber`. Let `ι : S ⥤ Type w` be a full subcategory of the category of sets in which some
object `pt` is a singleton, let `K` be the topology on `S` whose covering sieves are the jointly
surjective ones, and suppose the fibre functor factors as `u ⋙ ι` for some `u : C ⥤ S`. Then

1. there is an equivalence `i : Sh(pt) → Sh(S, K)` whose inverse image is `F ↦ F(pt)`, hence
   whose forward functor sends a set `E` to the sheaf `V ↦ Mor(ι V, E)`;
2. `u : C ⥤ S` defines a morphism of sites `f : (S, K) → (C, J)`; and
3. the composition `Sh(pt) → Sh(S, K) → Sh(C, J)` is the morphism of topoi `(p_*, p⁻¹)` of the
   point, in the sense that `i_* ⋙ f_*` is isomorphic to the skyscraper sheaf functor `p_*`. -/
@[stacks 04EL]
public theorem exists_equivalence_isMorphismOfSites_pushforward_iso {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} [LocallySmall.{w} C] (Φ : Point.{w} J) {S : Type w}
    [SmallCategory S] (ι : S ⥤ Type w) [ι.Full] [ι.Faithful] (pt : S) (hpt : Unique (ι.obj pt))
    (K : GrothendieckTopology S)
    (hK :
      ∀ (V : S) (R : Sieve V),
        R ∈ K V ↔ ∀ x : ι.obj V, ∃ (W : S) (f : W ⟶ V) (y : ι.obj W), R.arrows f ∧ ι.map f y = x)
    (u : C ⥤ S) (hu : u ⋙ ι ≅ Φ.fiber) :
    ∃ (e : Type w ≌ Sheaf K (Type w)) (_ : _root_.IsMorphismOfSites.{w} u J K),
      e.inverse = sheafToPresheaf K (Type w) ⋙ (evaluation Sᵒᵖ (Type w)).obj (Opposite.op pt) ∧
        Nonempty
          (e.functor ⋙ u.sheafPushforwardContinuous (Type w) J K ≅
            Φ.skyscraperSheafFunctor (A := Type w)) := by
  let := hpt
  have := isContinuous ι pt K hK Φ u hu
  have key :
    (setEquiv ι pt K hK).functor ⋙ u.sheafPushforwardContinuous (Type w) J K ≅
      Φ.skyscraperSheafFunctor (A := Type w) := by
    rw [setEquiv_functor]
    exact pushforwardSkyscraperIso ι pt K hK Φ u hu
  refine
    ⟨setEquiv ι pt K hK, ⟨Φ.sheafFiber ⋙ (setEquiv ι pt K hK).functor, ⟨?_⟩, ?_⟩,
      setEquiv_inverse ι pt K hK, ⟨key⟩⟩
  · refine (Φ.skyscraperSheafAdjunction.comp (setEquiv ι pt K hK).toAdjunction).ofNatIsoRight ?_
    exact
      (Functor.isoWhiskerLeft (setEquiv ι pt K hK).inverse key).symm ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (setEquiv ι pt K hK).counitIso _ ≪≫ Functor.leftUnitor _
  · exact comp_preservesFiniteLimits _ _

end

end CategoryTheory.GrothendieckTopology.Point

end
