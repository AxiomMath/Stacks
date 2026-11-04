module

public import Mathlib.Geometry.RingedSpace.OpenImmersion
public import Mathlib.Topology.ContinuousMap.Basic
public import StacksFrontier.Geometry.Sheaves.Amalgamation

/-!
# Morphisms of presheafed spaces glue along an open cover of the source

Let `X` and `Y` be presheafed spaces, let `U` be a family of open subsets covering `X`, and
suppose given morphisms `f i : X|_{U i} ⟶ Y` which agree on the overlaps `U i ⊓ U j`. If the
presheaf of `X` is a sheaf, then there is a unique morphism `f : X ⟶ Y` restricting to each
`f i`. This is the Zariski half of the statement that the functor of points of `Y` is a sheaf.

The construction of `f` has two independent halves. The underlying continuous map is glued
topologically, by `ContinuousMap.liftCover`; this uses only that the `U i` are open and cover
`X`. The map on sections is glued by the sheaf axiom for the presheaf of `X`, in the form
`TopCat.Presheaf.exists_amalgamation`: over an open `W` of `Y` the preimage `f⁻¹ W` is covered by
the opens `f⁻¹ W ⊓ U i`, on each of which `f i` already prescribes a map from `Y(W)`.

## Main definitions

* `AlgebraicGeometry.PresheafedSpace.resLE`: for open subsets `V ≤ W` of a presheafed space `X`,
  the morphism `X|_V ⟶ X|_W` restricting along the inclusion. It is an open immersion.
* `AlgebraicGeometry.PresheafedSpace.secOf`: the map on sections `Y(W) ⟶ X(V)` attached to a
  morphism `X|_V ⟶ Y` whose image lies in `W`.
* `AlgebraicGeometry.PresheafedSpace.glueBase`: the glued continuous map.

## Main results

* `AlgebraicGeometry.PresheafedSpace.hom_ext_of_openCover`: a morphism out of `X` is determined
  by its restrictions to the members of an open cover of `X`.
* `AlgebraicGeometry.PresheafedSpace.existsUnique_hom_of_openCover`: morphisms out of the members
  of an open cover of `X` agreeing on overlaps glue to a unique morphism out of `X`.

## Implementation notes

The compatibility hypothesis is phrased with `resLE`, as the equality of the two composites
`X|_{U i ⊓ U j} ⟶ X|_{U i} ⟶ Y` and `X|_{U i ⊓ U j} ⟶ X|_{U j} ⟶ Y`. Every restriction map
appearing below is `resLE` or a restriction map of the presheaf of `X`, and all of these are
inclusions of open subsets; since the inclusions between two fixed open subsets form a
subsingleton, the bookkeeping is carried out by `TopCat.Presheaf.map_comp_map`, which identifies
any two composites with the same source and target. The one place where an `eqToHom` is forced,
namely the comparison of the two `c`-components of morphisms whose underlying maps are only
propositionally equal, is absorbed by quantifying over the comparison map:
`hom_ext_of_base_eq` and `TopCat.Presheaf.res_eq_of_res_eq` both take it as an argument.

## References

* [Stacks Project, Tag 0AI2](https://stacks.math.columbia.edu/tag/0AI2)
-/

@[expose] public section

universe v u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Topology
open TopCat.Presheaf

namespace AlgebraicGeometry.PresheafedSpace

variable {C : Type u} [Category.{v} C]

/-- Two morphisms of presheafed spaces with equal underlying maps are equal as soon as their
`c`-components agree after a comparison map; the comparison map is quantified over, so that any
`eqToHom` identifying the two preimages of an open subset of the target will do. -/
theorem hom_ext_of_base_eq {X Y : PresheafedSpace.{v, u, w} C} {α β : X ⟶ Y}
    (w : α.base = β.base)
    (hc : ∀ (W : Opens (Y : TopCat))
        (m : op ((Opens.map α.base).obj W) ⟶ op ((Opens.map β.base).obj W)),
      α.c.app (op W) ≫ X.presheaf.map m = β.c.app (op W)) :
    α = β :=
  PresheafedSpace.ext α β w (NatTrans.ext (funext fun W => hc W.unop _))

section ResLE

/-- The image in `X` of an open subset of `V` cut out from an open subset of `W` is contained in
the image in `X` of the latter, for `V ≤ W` open subsets of `X`. -/
theorem functor_obj_inclusion_le (X : PresheafedSpace.{v, u, w} C) {V W : Opens (X : TopCat)}
    (h : V ≤ W) (O : Opens ((Opens.toTopCat (X : TopCat)).obj W)) :
    V.isOpenEmbedding.functor.obj
        ((Opens.map ((Opens.toTopCat (X : TopCat)).map (homOfLE h))).obj O)
      ≤ W.isOpenEmbedding.functor.obj O := by
  rintro x ⟨v, hv, rfl⟩
  exact ⟨⟨v.1, h v.2⟩, hv, rfl⟩

/-- The natural transformation of `Opens`-valued functors underlying the `c`-component of
`AlgebraicGeometry.PresheafedSpace.resLE`. -/
def resLENatTrans (X : PresheafedSpace.{v, u, w} C) {V W : Opens (X : TopCat)} (h : V ≤ W) :
    (Opens.map ((Opens.toTopCat (X : TopCat)).map (homOfLE h)) ⋙ V.isOpenEmbedding.functor)
      ⟶ W.isOpenEmbedding.functor where
  app O := homOfLE (X.functor_obj_inclusion_le h O)
  naturality _ _ _ := rfl

/-- For open subsets `V ≤ W` of a presheafed space `X`, the morphism `X|_V ⟶ X|_W` whose
underlying map is the inclusion and whose map on sections is restriction. -/
def resLE (X : PresheafedSpace.{v, u, w} C) {V W : Opens (X : TopCat)} (h : V ≤ W) :
    X.restrict V.isOpenEmbedding ⟶ X.restrict W.isOpenEmbedding where
  base := (Opens.toTopCat (X : TopCat)).map (homOfLE h)
  c := Functor.whiskerRight (NatTrans.op (X.resLENatTrans h)) X.presheaf

/-- The underlying map of `resLE h` is the inclusion of `V` into `W`. -/
@[simp]
theorem resLE_base (X : PresheafedSpace.{v, u, w} C) {V W : Opens (X : TopCat)} (h : V ≤ W) :
    (X.resLE h).base = (Opens.toTopCat (X : TopCat)).map (homOfLE h) := rfl

/-- The `c`-component of `resLE h` at an open subset `O` of `W` is the restriction map of the
presheaf of `X` from the image of `O` to the image of its preimage in `V`. -/
theorem resLE_c_app (X : PresheafedSpace.{v, u, w} C) {V W : Opens (X : TopCat)} (h : V ≤ W)
    (O : (Opens ((Opens.toTopCat (X : TopCat)).obj W))ᵒᵖ) :
    (X.resLE h).c.app O
      = X.presheaf.map (homOfLE (X.functor_obj_inclusion_le h O.unop)).op := rfl

/-- The underlying map of `resLE h` sends a point of `V` to the same point of `X`. -/
@[simp]
theorem resLE_base_apply (X : PresheafedSpace.{v, u, w} C) {V W : Opens (X : TopCat)} (h : V ≤ W)
    (x : V) : ((X.resLE h).base x).1 = x.1 := rfl

/-- For open subsets `V ≤ W ≤ T`, the composite `X|_V ⟶ X|_W ⟶ X|_T` is `X|_V ⟶ X|_T`. -/
theorem resLE_comp_resLE (X : PresheafedSpace.{v, u, w} C) {V W T : Opens (X : TopCat)}
    (h₁ : V ≤ W) (h₂ : W ≤ T) : X.resLE h₁ ≫ X.resLE h₂ = X.resLE (h₁.trans h₂) := by
  refine PresheafedSpace.hext _ _ rfl (heq_of_eq ?_)
  exact NatTrans.ext (funext fun _ => map_comp_map X.presheaf _ _ _)

/-- For open subsets `V ≤ W`, the composite `X|_V ⟶ X|_W ⟶ X` is the inclusion `X|_V ⟶ X`. -/
theorem resLE_comp_ofRestrict (X : PresheafedSpace.{v, u, w} C) {V W : Opens (X : TopCat)}
    (h : V ≤ W) :
    X.resLE h ≫ X.ofRestrict W.isOpenEmbedding = X.ofRestrict V.isOpenEmbedding := by
  refine PresheafedSpace.hext _ _ rfl (heq_of_eq ?_)
  exact NatTrans.ext (funext fun _ => map_comp_map X.presheaf _ _ _)

/-- Membership in the preimage of an open subset, unfolded. -/
theorem mem_opens_map {Z T : TopCat.{w}} (g : Z ⟶ T) (W : Opens T) (x : Z) :
    x ∈ ((Opens.map g).obj W : Set Z) ↔ g x ∈ W := Iff.rfl

/-- The underlying map of `resLE h` is an open embedding. -/
theorem isOpenEmbedding_resLE_base (X : PresheafedSpace.{v, u, w} C) {V W : Opens (X : TopCat)}
    (h : V ≤ W) : IsOpenEmbedding (X.resLE h).base :=
  IsOpenEmbedding.of_comp _ W.2.isOpenEmbedding_subtypeVal V.2.isOpenEmbedding_subtypeVal

/-- The morphism `resLE h : X|_V ⟶ X|_W` is an open immersion. -/
instance isOpenImmersion_resLE (X : PresheafedSpace.{v, u, w} C) {V W : Opens (X : TopCat)}
    (h : V ≤ W) : PresheafedSpace.IsOpenImmersion (X.resLE h) where
  base_open := X.isOpenEmbedding_resLE_base h
  c_iso O := by
    refine isIso_map_of_eq X.presheaf _ (le_antisymm (X.functor_obj_inclusion_le h _) ?_)
    rintro z ⟨w, ⟨o, hoO, rfl⟩, rfl⟩
    exact ⟨o, ⟨o, hoO, rfl⟩, rfl⟩

end ResLE

section SecOf

variable {X Y : PresheafedSpace.{v, u, w} C}

/-- Two restriction maps of a presheaf following a morphism compose to a single restriction. -/
private theorem comp_map_comp_map {T : TopCat.{w}} (F : (Opens T)ᵒᵖ ⥤ C) {Z : C}
    {A B D : (Opens T)ᵒᵖ} (φ : Z ⟶ F.obj A) {a : A ⟶ B} {b : B ⟶ D} (c : A ⟶ D) :
    (φ ≫ F.map a) ≫ F.map b = φ ≫ F.map c := by
  rw [Category.assoc, map_comp_map]

/-- If a morphism `g : X|_V ⟶ Y` maps `V` into the open subset `W` of `Y`, then `V` is contained
in the image in `X` of the preimage of `W`. -/
theorem le_functor_obj_map_base {V : Opens (X : TopCat)}
    (g : X.restrict V.isOpenEmbedding ⟶ Y) (W : Opens (Y : TopCat))
    (hg : ∀ x : (X.restrict V.isOpenEmbedding : TopCat), g.base x ∈ W) :
    V ≤ V.isOpenEmbedding.functor.obj ((Opens.map g.base).obj W) :=
  fun x hx => ⟨⟨x, hx⟩, hg ⟨x, hx⟩, rfl⟩

/-- The map on sections `Y(W) ⟶ X(V)` attached to a morphism `g : X|_V ⟶ Y` carrying `V` into
the open subset `W` of `Y`. -/
def secOf {V : Opens (X : TopCat)} (g : X.restrict V.isOpenEmbedding ⟶ Y)
    (W : Opens (Y : TopCat))
    (hg : V ≤ V.isOpenEmbedding.functor.obj ((Opens.map g.base).obj W)) :
    Y.presheaf.obj (op W) ⟶ X.presheaf.obj (op V) :=
  g.c.app (op W) ≫ X.presheaf.map (homOfLE hg).op

/-- The sections map `secOf g W hg` depends only on the morphism `g`. -/
theorem secOf_congr {V : Opens (X : TopCat)} {g g' : X.restrict V.isOpenEmbedding ⟶ Y}
    (W : Opens (Y : TopCat)) (hg) (hg') (e : g = g') : secOf g W hg = secOf g' W hg' := by
  subst e; rfl

/-- Restricting the sections map of `g : X|_V ⟶ Y` to `V' ≤ V` gives the sections map of the
composite `X|_{V'} ⟶ X|_V ⟶ Y`. -/
theorem secOf_res {V V' : Opens (X : TopCat)} (h : V' ≤ V)
    (g : X.restrict V.isOpenEmbedding ⟶ Y) (W : Opens (Y : TopCat)) (hg) (hg') :
    secOf g W hg ≫ X.presheaf.map (homOfLE h).op = secOf (X.resLE h ≫ g) W hg' :=
  (comp_map_comp_map X.presheaf (g.c.app (op W)) (homOfLE (h.trans hg)).op).trans
    (comp_map_comp_map X.presheaf (g.c.app (op W)) (homOfLE (h.trans hg)).op).symm

/-- The sections maps of `g` are compatible with the restriction maps of the presheaf of `Y`: for
`W' ≤ W`, restricting from `W` to `W'` and then applying `secOf g W'` is `secOf g W`. -/
theorem secOf_map {V : Opens (X : TopCat)} (g : X.restrict V.isOpenEmbedding ⟶ Y)
    {W W' : Opens (Y : TopCat)} (h : W' ≤ W) (hg) (hg') :
    Y.presheaf.map (homOfLE h).op ≫ secOf g W' hg' = secOf g W hg :=
  Eq.trans (Category.assoc _ _ _).symm (Eq.trans
    (congrArg (fun m => m ≫ X.presheaf.map (homOfLE hg').op) (g.c.naturality (homOfLE h).op))
    (Eq.trans (Category.assoc _ _ _)
      (congrArg (fun m => g.c.app (op W) ≫ m)
        (map_comp_map X.presheaf _ _ (homOfLE hg).op))))

/-- The sections map of `X|_{V'} ⟶ X|_V ⟶ Y` is the sections map of `X|_V ⟶ Y` followed by
restriction. -/
theorem secOf_resLE {V V' : Opens (X : TopCat)} (h : V' ≤ V)
    (g : X.restrict V.isOpenEmbedding ⟶ Y) (W : Opens (Y : TopCat)) (hg)
    (hVT : V' ≤ V.isOpenEmbedding.functor.obj ((Opens.map g.base).obj W)) :
    secOf (X.resLE h ≫ g) W hg = g.c.app (op W) ≫ X.presheaf.map (homOfLE hVT).op :=
  comp_map_comp_map X.presheaf (g.c.app (op W)) _

/-- The sections map of `X|_V ⟶ X ⟶ Y` is the sections map of `X ⟶ Y` followed by
restriction to `V`. -/
theorem secOf_ofRestrict_comp {g : X ⟶ Y} {V : Opens (X : TopCat)} {W : Opens (Y : TopCat)} (hg)
    (hVP : V ≤ (Opens.map g.base).obj W) :
    secOf (X.ofRestrict V.isOpenEmbedding ≫ g) W hg
      = g.c.app (op W) ≫ X.presheaf.map (homOfLE hVP).op :=
  comp_map_comp_map X.presheaf (g.c.app (op W)) _

end SecOf

section Glue

variable {X Y : PresheafedSpace.{v, u, w} C} {ι : Type*} (U : ι → Opens (X : TopCat))

/-- An open subset contained in an open subset `P` and in a member `U i` of a family is contained
in the image in `X` of the preimage of `P` in `U i`. -/
theorem le_functor_obj_map_inclusion {V P : Opens (X : TopCat)} {i : ι} (hVP : V ≤ P)
    (hVU : V ≤ U i) :
    V ≤ (U i).isOpenEmbedding.functor.obj ((Opens.map (U i).inclusion').obj P) := by
  rw [Opens.functor_map_eq_inf]
  exact le_inf hVP hVU

/-- Restricting the sections map of `X|_{U i} ⟶ X ⟶ Y` to a small enough open subset recovers
the sections map of `X ⟶ Y`. -/
theorem ofRestrict_comp_c_app_res {g : X ⟶ Y} {i : ι} {W : Opens (Y : TopCat)}
    {V : Opens (X : TopCat)} (hVP : V ≤ (Opens.map g.base).obj W) (hVU : V ≤ U i) :
    (X.ofRestrict (U i).isOpenEmbedding ≫ g).c.app (op W)
        ≫ X.presheaf.map (homOfLE (le_functor_obj_map_inclusion U hVP hVU)).op
      = g.c.app (op W) ≫ X.presheaf.map (homOfLE hVP).op :=
  comp_map_comp_map X.presheaf (g.c.app (op W)) _

variable (hU : iSup U = ⊤)

include hU in
/-- Every point of `X` lies in some member of an open cover of `X`. -/
theorem exists_mem_of_openCover (x : (X : TopCat)) : ∃ i, x ∈ U i :=
  Opens.mem_iSup.mp (hU.ge (Opens.mem_top x))

include hU in
/-- The union of the preimages in the members of an open cover of an open subset `P` of `X`
is `P`. -/
theorem iSup_inf_eq_self (P : Opens (X : TopCat)) : (iSup fun i => P ⊓ U i) = P := by
  rw [← inf_iSup_eq, hU, inf_top_eq]

include hU in
/-- **Separatedness.** A morphism out of a presheafed space whose presheaf is a sheaf is
determined by its restrictions to the members of an open cover of the source. -/
theorem hom_ext_of_openCover (hX : X.presheaf.IsSheaf) {g₁ g₂ : X ⟶ Y}
    (h : ∀ i, X.ofRestrict (U i).isOpenEmbedding ≫ g₁
            = X.ofRestrict (U i).isOpenEmbedding ≫ g₂) :
    g₁ = g₂ := by
  have hbase : g₁.base = g₂.base := by
    refine TopCat.hom_ext (ContinuousMap.ext fun x => ?_)
    obtain ⟨i, hi⟩ := exists_mem_of_openCover U hU x
    have e := congrArg (fun m : X.restrict (U i).isOpenEmbedding ⟶ Y => m ⟨x, hi⟩) (h i)
    exact e
  refine hom_ext_of_base_eq hbase fun W m => ?_
  have hP : (Opens.map g₁.base).obj W = (Opens.map g₂.base).obj W := by rw [hbase]
  have key : ∀ (V : Opens (X : TopCat)) (_ : ∃ i, V ≤ (Opens.map g₂.base).obj W ⊓ U i)
      (hVP : V ≤ (Opens.map g₂.base).obj W),
      (g₁.c.app (op W) ≫ X.presheaf.map (homOfLE hP.ge).op) ≫ X.presheaf.map (homOfLE hVP).op
        = (g₂.c.app (op W) ≫ X.presheaf.map (homOfLE (le_refl _)).op)
            ≫ X.presheaf.map (homOfLE hVP).op := by
    intro V hV hVP
    obtain ⟨i, hVi⟩ := hV
    have hVU : V ≤ U i := hVi.trans inf_le_right
    have hVP₁ : V ≤ (Opens.map g₁.base).obj W := le_trans hVP hP.ge
    have e₃ : X.ofRestrict V.isOpenEmbedding ≫ g₁ = X.ofRestrict V.isOpenEmbedding ≫ g₂ := by
      rw [← X.resLE_comp_ofRestrict hVU, Category.assoc, Category.assoc, h i]
    have hg₁ : V ≤ V.isOpenEmbedding.functor.obj
        ((Opens.map (X.ofRestrict V.isOpenEmbedding ≫ g₁).base).obj W) :=
      le_functor_obj_map_base _ W fun x => hVP₁ x.2
    have hg₂ : V ≤ V.isOpenEmbedding.functor.obj
        ((Opens.map (X.ofRestrict V.isOpenEmbedding ≫ g₂).base).obj W) :=
      le_functor_obj_map_base _ W fun x => hVP x.2
    rw [comp_map_comp_map _ _ (homOfLE hVP₁).op, comp_map_comp_map _ _ (homOfLE hVP).op,
      ← secOf_ofRestrict_comp hg₁ hVP₁, ← secOf_ofRestrict_comp hg₂ hVP]
    exact secOf_congr W hg₁ hg₂ e₃
  have hres := amalgamation_unique hX (fun i => (Opens.map g₂.base).obj W ⊓ U i)
    (iSup_inf_eq_self U hU _) key
  exact res_eq_of_res_eq X.presheaf (g₁.c.app (op W)) (g₂.c.app (op W)) (le_refl _) (le_refl _)
    hP.ge hres m

variable (f : ∀ i, X.restrict (U i).isOpenEmbedding ⟶ Y)
  (hf : ∀ i j, X.resLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ f i
      = X.resLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ f j)

include hf in
/-- The compatibility of the `f i` on the pairwise overlaps spreads to every open subset
contained in two members of the cover. -/
theorem resLE_comp_eq {V : Opens (X : TopCat)} (i j : ι) (hi : V ≤ U i) (hj : V ≤ U j) :
    X.resLE hi ≫ f i = X.resLE hj ≫ f j := by
  have hij : V ≤ U i ⊓ U j := le_inf hi hj
  have e₁ : X.resLE hi = X.resLE hij ≫ X.resLE (inf_le_left : U i ⊓ U j ≤ U i) :=
    (X.resLE_comp_resLE hij inf_le_left).symm
  have e₂ : X.resLE hj = X.resLE hij ≫ X.resLE (inf_le_right : U i ⊓ U j ≤ U j) :=
    (X.resLE_comp_resLE hij inf_le_right).symm
  rw [e₁, e₂, Category.assoc, Category.assoc, hf i j]

include hf in
/-- At a point of `U i ⊓ U j`, the underlying maps of `f i` and `f j` take the same value. -/
theorem base_apply_eq (i j : ι) (x : (X : TopCat)) (hxi : x ∈ U i) (hxj : x ∈ U j) :
    (f i) ⟨x, hxi⟩ = (f j) ⟨x, hxj⟩ := by
  have e := congrArg (fun m : X.restrict (U i ⊓ U j).isOpenEmbedding ⟶ Y => m ⟨x, hxi, hxj⟩)
    (hf i j)
  exact e

include hU in
/-- Each member of an open cover is a neighbourhood of each of its points. -/
theorem openCover_mem_nhds :
    ∀ x : (X : TopCat), ∃ i, (U i : Set (X : TopCat)) ∈ 𝓝 x := fun x =>
  let ⟨i, hi⟩ := exists_mem_of_openCover U hU x
  ⟨i, (U i).isOpen.mem_nhds hi⟩

/-- The continuous map obtained by gluing the underlying maps of a compatible family of morphisms
out of the members of an open cover. -/
noncomputable def glueBase : (X : TopCat) ⟶ (Y : TopCat) :=
  TopCat.ofHom (ContinuousMap.liftCover (fun i => (U i : Set (X : TopCat)))
    (fun i => TopCat.Hom.hom (f i).base) (base_apply_eq U f hf) (openCover_mem_nhds U hU))

/-- On a point of `U i`, the glued map agrees with the underlying map of `f i`. -/
@[simp]
theorem glueBase_apply (i : ι) (x : (X : TopCat)) (hx : x ∈ U i) :
    glueBase U hU f hf x = (f i) ⟨x, hx⟩ :=
  ContinuousMap.liftCover_coe (S := fun i => (U i : Set (X : TopCat)))
    (φ := fun i => TopCat.Hom.hom (f i).base) (hφ := base_apply_eq U f hf)
    (hS := openCover_mem_nhds U hU) (i := i) ⟨x, hx⟩

/-- The hypothesis of `AlgebraicGeometry.PresheafedSpace.secOf` for the restriction of `f i` to a
small open subset. -/
theorem le_functor_obj_resLE_comp {W : Opens (Y : TopCat)} {V : Opens (X : TopCat)} (i : ι)
    (hiV : V ≤ U i) (hVP : V ≤ (Opens.map (glueBase U hU f hf)).obj W) :
    V ≤ V.isOpenEmbedding.functor.obj ((Opens.map (X.resLE hiV ≫ f i).base).obj W) := by
  refine le_functor_obj_map_base (X.resLE hiV ≫ f i) W fun x => ?_
  have e : (X.resLE hiV ≫ f i).base x = glueBase U hU f hf x.1 :=
    (glueBase_apply U hU f hf i x.1 (hiV x.2)).symm
  rw [e]
  exact hVP x.2

/-- The map on sections over `W` prescribed on a small open subset `V` by the member `f i` of the
family. -/
noncomputable def glueSec (W : Opens (Y : TopCat)) {V : Opens (X : TopCat)} (i : ι)
    (hiV : V ≤ U i) (hVP : V ≤ (Opens.map (glueBase U hU f hf)).obj W) :
    Y.presheaf.obj (op W) ⟶ X.presheaf.obj (op V) :=
  secOf (X.resLE hiV ≫ f i) W (le_functor_obj_resLE_comp U hU f hf i hiV hVP)

/-- The map on sections `glueSec` does not depend on the member `U i` containing `V`. -/
theorem glueSec_indep (W : Opens (Y : TopCat)) {V : Opens (X : TopCat)} (i j : ι)
    (hiV : V ≤ U i) (hjV : V ≤ U j) (hVP : V ≤ (Opens.map (glueBase U hU f hf)).obj W) :
    glueSec U hU f hf W i hiV hVP = glueSec U hU f hf W j hjV hVP :=
  secOf_congr _ _ _ (resLE_comp_eq U f hf i j hiV hjV)

/-- Restricting `glueSec` from `V` to `V' ≤ V` gives `glueSec` on `V'`. -/
theorem glueSec_res (W : Opens (Y : TopCat)) {V V' : Opens (X : TopCat)} (i : ι)
    (hiV : V ≤ U i) (hVP : V ≤ (Opens.map (glueBase U hU f hf)).obj W) (h : V' ≤ V) :
    glueSec U hU f hf W i hiV hVP ≫ X.presheaf.map (homOfLE h).op
      = glueSec U hU f hf W i (h.trans hiV) (h.trans hVP) := by
  refine Eq.trans (secOf_res h _ W _ ?_) (secOf_congr _ _ _ ?_)
  · exact le_functor_obj_resLE_comp U hU f hf i (h.trans hiV) (h.trans hVP)
  · rw [← Category.assoc, X.resLE_comp_resLE]

/-- The maps `glueSec` are compatible with the restriction maps of the presheaf of `Y`. -/
theorem glueSec_map {W W' : Opens (Y : TopCat)} (hW : W' ≤ W) {V : Opens (X : TopCat)} (i : ι)
    (hiV : V ≤ U i) (hVP : V ≤ (Opens.map (glueBase U hU f hf)).obj W)
    (hVP' : V ≤ (Opens.map (glueBase U hU f hf)).obj W') :
    Y.presheaf.map (homOfLE hW).op ≫ glueSec U hU f hf W' i hiV hVP'
      = glueSec U hU f hf W i hiV hVP :=
  secOf_map _ hW _ _

include hf hU in
/-- Over an open subset `W` of `Y`, the maps prescribed by the members of the family amalgamate
to a single map `Y(W) ⟶ X(f⁻¹ W)`. -/
theorem exists_glueC (hX : X.presheaf.IsSheaf) (W : Opens (Y : TopCat)) :
    ∃ t : Y.presheaf.obj (op W) ⟶ X.presheaf.obj (op ((Opens.map (glueBase U hU f hf)).obj W)),
      ∀ (V : Opens (X : TopCat)) (i : ι) (hiV : V ≤ U i)
        (hVP : V ≤ (Opens.map (glueBase U hU f hf)).obj W),
        t ≫ X.presheaf.map (homOfLE hVP).op = glueSec U hU f hf W i hiV hVP := by
  set P := (Opens.map (glueBase U hU f hf)).obj W with hPdef
  refine Exists.imp ?_ (exists_amalgamation hX (fun i => P ⊓ U i) (iSup_inf_eq_self U hU P)
    (fun V hV => glueSec U hU f hf W hV.choose (hV.choose_spec.trans inf_le_right)
      (hV.choose_spec.trans inf_le_left)) ?_)
  · intro t ht V i hiV hVP
    have hV : ∃ k, V ≤ P ⊓ U k := ⟨i, le_inf hVP hiV⟩
    have h1 := ht V hV hVP
    have h2 : glueSec U hU f hf W hV.choose (hV.choose_spec.trans inf_le_right)
          (hV.choose_spec.trans inf_le_left)
        = glueSec U hU f hf W i hiV (hV.choose_spec.trans inf_le_left) :=
      glueSec_indep U hU f hf W hV.choose i (hV.choose_spec.trans inf_le_right) hiV
        (hV.choose_spec.trans inf_le_left)
    exact h1.trans h2
  · intro V V' hV hV' h
    have h1 := glueSec_res U hU f hf W hV.choose (hV.choose_spec.trans inf_le_right)
      (hV.choose_spec.trans inf_le_left) h
    have h2 : glueSec U hU f hf W hV.choose (h.trans (hV.choose_spec.trans inf_le_right))
          (h.trans (hV.choose_spec.trans inf_le_left))
        = glueSec U hU f hf W hV'.choose (hV'.choose_spec.trans inf_le_right)
          (h.trans (hV.choose_spec.trans inf_le_left)) :=
      glueSec_indep U hU f hf W hV.choose hV'.choose
        (h.trans (hV.choose_spec.trans inf_le_right)) (hV'.choose_spec.trans inf_le_right)
        (h.trans (hV.choose_spec.trans inf_le_left))
    exact h1.trans h2

include hf hU in
/-- The preimage of an open subset `W` of `Y` under `f i` is the intersection of `U i` with the
preimage of `W` under the glued map. -/
theorem functor_obj_preimage_eq (i : ι) (W : Opens (Y : TopCat)) :
    (U i).isOpenEmbedding.functor.obj ((Opens.map (f i).base).obj W)
      = (Opens.map (glueBase U hU f hf)).obj W ⊓ U i := by
  refine le_antisymm ?_ ?_
  · rintro z ⟨p, hp, rfl⟩
    refine ⟨?_, p.2⟩
    refine (mem_opens_map _ W _).mpr ?_
    have e := glueBase_apply U hU f hf i ((U i).inclusion' p) p.2
    rw [e]
    exact hp
  · intro z hz
    obtain ⟨hzP, hzU⟩ := hz
    refine ⟨⟨z, hzU⟩, ?_, rfl⟩
    refine (mem_opens_map _ W _).mpr ?_
    have e := glueBase_apply U hU f hf i z hzU
    rw [← e]
    exact hzP

include hf hU in
/-- **Morphisms of presheafed spaces glue along an open cover of the source.** Let `X` be a
presheafed space whose presheaf is a sheaf, let `U` be a family of open subsets covering `X`, and
let `f i : X|_{U i} ⟶ Y` be morphisms agreeing on the overlaps `U i ⊓ U j`. Then there is a
unique morphism `X ⟶ Y` restricting to `f i` on each `U i`.

This is the Zariski sheaf condition for the functor of points of `Y`. -/
theorem existsUnique_hom_of_openCover (hX : X.presheaf.IsSheaf) :
    ∃! g : X ⟶ Y, ∀ i, X.ofRestrict (U i).isOpenEmbedding ≫ g = f i := by
  choose t ht using exists_glueC U hU f hf hX
  have hnat : ∀ (W₁ W₂ : (Opens (Y : TopCat))ᵒᵖ) (m : W₁ ⟶ W₂),
      Y.presheaf.map m ≫ t W₂.unop
        = t W₁.unop ≫ ((glueBase U hU f hf) _* X.presheaf).map m := by
    intro W₁ W₂ m
    have hW : W₂.unop ≤ W₁.unop := leOfHom m.unop
    refine amalgamation_unique hX (fun i => (Opens.map (glueBase U hU f hf)).obj W₂.unop ⊓ U i)
      (iSup_inf_eq_self U hU _) fun V hV hVP => ?_
    obtain ⟨i, hVi⟩ := hV
    have hVU : V ≤ U i := hVi.trans inf_le_right
    have hVP₁ : V ≤ (Opens.map (glueBase U hU f hf)).obj W₁.unop := fun x hx => hW (hVP hx)
    have e₂' : ((glueBase U hU f hf) _* X.presheaf).map m ≫ X.presheaf.map (homOfLE hVP).op
        = X.presheaf.map (homOfLE hVP₁).op :=
      map_comp_map X.presheaf _ _ (homOfLE hVP₁).op
    rw [Category.assoc, Category.assoc, e₂', ht W₂.unop V i hVU hVP,
      ht W₁.unop V i hVU hVP₁]
    exact glueSec_map U hU f hf hW i hVU hVP₁ hVP
  set g : X ⟶ Y := ⟨glueBase U hU f hf, { app := fun W => t W.unop, naturality := hnat }⟩ with hg
  have hgc : ∀ W : Opens (Y : TopCat), g.c.app (op W) = t W := fun _ => rfl
  have hfac : ∀ i, X.ofRestrict (U i).isOpenEmbedding ≫ g = f i := by
    intro i
    have hbase : (X.ofRestrict (U i).isOpenEmbedding ≫ g).base = (f i).base := by
      refine TopCat.hom_ext (ContinuousMap.ext fun p => ?_)
      exact glueBase_apply U hU f hf i p.1 p.2
    refine hom_ext_of_base_eq hbase fun W m => ?_
    have hVT : (Opens.map (glueBase U hU f hf)).obj W ⊓ U i
        ≤ (U i).isOpenEmbedding.functor.obj ((Opens.map (f i).base).obj W) :=
      (functor_obj_preimage_eq U hU f hf i W).ge
    have hTV : (U i).isOpenEmbedding.functor.obj ((Opens.map (f i).base).obj W)
        ≤ (Opens.map (glueBase U hU f hf)).obj W ⊓ U i :=
      (functor_obj_preimage_eq U hU f hf i W).le
    refine res_eq_of_res_eq X.presheaf _ ((f i).c.app (op W)) hVT hTV
      (le_functor_obj_map_inclusion U (inf_le_left) (inf_le_right)) ?_
      ((U i).isOpenEmbedding.functor.op.map m)
    have e₁ := ofRestrict_comp_c_app_res U (g := g)
      (inf_le_left : (Opens.map (glueBase U hU f hf)).obj W ⊓ U i
        ≤ (Opens.map g.base).obj W) (inf_le_right : _ ≤ U i)
    have e₂ := ht W ((Opens.map (glueBase U hU f hf)).obj W ⊓ U i) i inf_le_right inf_le_left
    have e₃ : glueSec U hU f hf W i (inf_le_right) (inf_le_left)
        = (f i).c.app (op W) ≫ X.presheaf.map (homOfLE hVT).op :=
      secOf_resLE _ _ W _ hVT
    refine e₁.trans ?_
    rw [hgc W, e₂, e₃]
    rfl
  refine ⟨g, hfac, fun g' hg' => ?_⟩
  exact hom_ext_of_openCover U hU hX fun i => (hg' i).trans (hfac i).symm

end Glue

end AlgebraicGeometry.PresheafedSpace

end
