module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.Topology.Sheaves.Limits
public import Mathlib.Topology.Sheaves.Sheafify
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sections of a filtered colimit of sheaves of sets

Let `X` be a topological space, let `I` be a filtered category whose objects form a `u`-small
type, and let `F : I ⥤ TopCat.Sheaf (Type u) X` be a system of sheaves of sets. Write
`ℱ' = colimitPresheaf F` for the colimit of the underlying presheaves, so that
`ℱ'(V) = colimᵢ ℱᵢ(V)`, and `colimitSheaf F` for its sheafification, the colimit of the system in
sheaves. The canonical map `Ψ : colimᵢ ℱᵢ(U) ⟶ (colimᵢ ℱᵢ)(U)` is `canonicalMap F U`, the
component at `U` of the unit `ℱ' ⟶ (ℱ')^#`. This file gives conditions under which `Ψ` is
injective or bijective.

## Main definitions

* `DirectedColimitOfSheaves.HasFiniteCompactCofinalCovers U`: every open covering of `U` is
  refined by a finite covering of `U` all of whose pairwise intersections are quasi-compact.
* `DirectedColimitOfSheaves.HasInjectiveTransitions F`: every transition map of the system is
  injective on sections over every open.
* `DirectedColimitOfSheaves.colimitPresheaf` and `DirectedColimitOfSheaves.colimitSheaf`: the
  colimit `ℱ'` of the underlying presheaves and its sheafification.
* `DirectedColimitOfSheaves.canonicalMap F U`: the canonical map `Ψ`.

## Main results

* `DirectedColimitOfSheaves.injective_canonicalMap_of_hasInjectiveTransitions`: if all the
  transition maps are injective, then `Ψ` is injective.
* `DirectedColimitOfSheaves.injective_canonicalMap_of_isCompact`: if `U` is quasi-compact, then
  `Ψ` is injective.
* `DirectedColimitOfSheaves.bijective_canonicalMap_of_isCompact_of_hasInjectiveTransitions`: if
  `U` is quasi-compact and all the transition maps are injective, then `Ψ` is bijective.
* `DirectedColimitOfSheaves.bijective_canonicalMap_of_hasFiniteCompactCofinalCovers`: if `U` has
  a cofinal system of finite open coverings with quasi-compact pairwise intersections, then `Ψ`
  is bijective.
* `DirectedColimitOfSheaves.hasInjectiveTransitions_of_le`: for a system indexed by a directed
  preorder, the transition maps are injective as soon as the maps `homOfLE h` are.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopCat Opposite

universe u v w

namespace DirectedColimitOfSheaves

variable {X : TopCat.{u}}

/-- `U` has a cofinal system of finite open coverings with quasi-compact pairwise
intersections: every open covering of `U` is refined by a finite covering of `U` all of whose
pairwise intersections are quasi-compact. -/
def HasFiniteCompactCofinalCovers (U : Opens X) : Prop :=
  ∀ {J : Type u} (V : J → Opens X),
    (∀ j, V j ≤ U) → (U ≤ ⨆ j, V j) →
      ∃ (K : Type u) (_ : Finite K) (W : K → Opens X),
        (∀ k, W k ≤ U) ∧
        (U ≤ ⨆ k, W k) ∧
        (∀ k, ∃ j, W k ≤ V j) ∧
        (∀ k k', IsCompact ((W k ⊓ W k') : Set X))

variable {I : Type v} [Category.{w} I] (F : I ⥤ TopCat.Sheaf (Type u) X)

/-- The system of presheaves of sets underlying a system of sheaves of sets: postcompose with
the forgetful functor from sheaves to presheaves. -/
noncomputable def presheafSystem : I ⥤ TopCat.Presheaf (Type u) X :=
  F ⋙ sheafToPresheaf (Opens.grothendieckTopology X) (Type u)

/-- All transition maps of the system are injective on sections over every open. -/
def HasInjectiveTransitions : Prop :=
  ∀ ⦃i i' : I⦄ (f : i ⟶ i') (V : Opens X),
    Function.Injective (((presheafSystem F).map f).app (op V))

/-- The system of sets obtained by evaluating the presheaf system at `U`, i.e. `i ↦ ℱᵢ(U)`. -/
noncomputable def evalSystem (U : Opens X) : I ⥤ Type u :=
  presheafSystem F ⋙ (evaluation _ _).obj (op U)

/-! ### The sheaf condition at a single index -/

/-- Uniqueness half of the sheaf condition for `ℱₖ`: two sections over `U` that agree on
every member of an open covering of `U` are equal. -/
lemma sheaf_eq_of_local_eq (k : I) (U : Opens X)
    {ι : Type u} (V : ι → Opens X) (hVU : ∀ j, V j ≤ U) (hcover : U ≤ ⨆ j, V j)
    (s t : ((presheafSystem F).obj k).obj (op U))
    (hrestr : ∀ j, ((presheafSystem F).obj k).map (homOfLE (hVU j)).op s =
                    ((presheafSystem F).obj k).map (homOfLE (hVU j)).op t) :
    s = t := by
  have hUeq : U = ⨆ j, V j := le_antisymm hcover (iSup_le hVU)
  subst hUeq
  exact Sheaf.eq_of_locally_eq (F.obj k) V s t hrestr

/-- Existence half of the sheaf condition for `ℱₖ`: sections over the members of an open
covering of `U` that agree on the pairwise intersections come from a section over `U`. -/
lemma sheaf_glue (k : I) (U : Opens X)
    {ι : Type u} (V : ι → Opens X) (hVU : ∀ j, V j ≤ U) (hcover : U ≤ ⨆ j, V j)
    (sections : ∀ j, ((presheafSystem F).obj k).obj (op (V j)))
    (compat : ∀ j j',
        ((presheafSystem F).obj k).map (homOfLE (inf_le_left (a := V j) (b := V j'))).op
          (sections j) =
        ((presheafSystem F).obj k).map (homOfLE (inf_le_right (a := V j) (b := V j'))).op
          (sections j')) :
    ∃ s : ((presheafSystem F).obj k).obj (op U),
      ∀ j, ((presheafSystem F).obj k).map (homOfLE (hVU j)).op s = sections j := by
  have hUeq : U = ⨆ j, V j := le_antisymm hcover (iSup_le hVU)
  subst hUeq
  obtain ⟨s, hs, _⟩ := Sheaf.existsUnique_gluing (F.obj k) V sections fun i j ↦ compat i j
  exact ⟨s, hs⟩

/-- Restricting along `V' ≤ V` commutes with the transition map `γ`. -/
private lemma map_restrict_app_eq {k k' : I} (γ : k ⟶ k') {V V' : Opens X} (hle : V' ≤ V)
    (x : ((presheafSystem F).obj k).obj (op V)) :
    ((presheafSystem F).obj k').map (homOfLE hle).op (((presheafSystem F).map γ).app (op V) x) =
    ((presheafSystem F).map γ).app (op V') (((presheafSystem F).obj k).map (homOfLE hle).op x) :=
  (ConcreteCategory.congr_hom (NatTrans.naturality ((presheafSystem F).map γ) (homOfLE hle).op)
    x).symm

/-! ### The colimit presheaf, its sheafification and the canonical map -/

variable [Small.{u} I]

/-- The colimit `ℱ'` of the underlying presheaves, whose sections over `U` are
`colimᵢ ℱᵢ(U)`. -/
@[implicit_reducible]
noncomputable def colimitPresheaf : TopCat.Presheaf (Type u) X :=
  colimit (presheafSystem F)

/-- The sheafification `(ℱ')^#` of the colimit presheaf, the colimit of the system `F` in the
category of sheaves of sets. -/
noncomputable def colimitSheaf : TopCat.Sheaf (Type u) X :=
  TopCat.Presheaf.sheafify (colimitPresheaf F)

/-- The canonical map `Ψ : colimᵢ ℱᵢ(U) ⟶ (colimᵢ ℱᵢ)(U)`, namely the component at `U` of the
unit `ℱ' ⟶ (ℱ')^#` of sheafification. -/
@[stacks 009F]
noncomputable def canonicalMap (U : Opens X) :
    (colimitPresheaf F).obj (op U) ⟶ (colimitSheaf F).obj.obj (op U) :=
  (TopCat.Presheaf.toSheafify (colimitPresheaf F)).app (op U)

/-- Two sections of `ℱ'` over `U` have the same image under `Ψ` if and only if their germs
agree at every point of `U`. -/
lemma canonicalMap_eq_iff (U : Opens X)
    (s t : (colimitPresheaf F).obj (op U)) :
    canonicalMap F U s = canonicalMap F U t ↔
    ∀ (x : X) (hx : x ∈ U),
      (colimitPresheaf F).germ U x hx s = (colimitPresheaf F).germ U x hx t := by
  refine ⟨fun h x hx ↦ congr_fun (congr_arg Subtype.val h) ⟨x, hx⟩, fun hgerm ↦ ?_⟩
  unfold canonicalMap colimitSheaf
  refine Presheaf.section_ext (Presheaf.sheafify (colimitPresheaf F)) U _ _ fun x hx ↦ ?_
  exact (Presheaf.stalkFunctor_map_germ_apply U x hx
    (Presheaf.toSheafify (colimitPresheaf F)) s).symm.trans (congr_arg _ (hgerm x hx)) |>.trans
      (Presheaf.stalkFunctor_map_germ_apply U x hx (Presheaf.toSheafify (colimitPresheaf F)) t)

/-- Every section of `(ℱ')^#` over `U` is locally in the image of `Ψ`: around each point of
`U` there is an open on which the section is the image of a section of `ℱ'`. -/
lemma exists_localPreimage (U : Opens X)
    (σ : (colimitSheaf F).obj.obj (op U)) (x : X) (hx : x ∈ U) :
    ∃ (V : Opens X) (_ : x ∈ V) (hVU : V ≤ U)
      (s : (colimitPresheaf F).obj (op V)),
      canonicalMap F V s = (colimitSheaf F).obj.map (homOfLE hVU).op σ := by
  obtain ⟨V, hxV, i, s, hs⟩ := σ.property ⟨x, hx⟩
  exact ⟨V, hxV, leOfHom i, s, Subtype.ext (funext fun y ↦ (hs y).symm)⟩

/-- `Ψ` commutes with restriction along `V' ≤ V`, on the sections coming from a single index
`j` of the system. -/
lemma canonicalMap_ι_restrict (j : I) (V V' : Opens X) (hle : V' ≤ V)
    (τ : ((presheafSystem F).obj j).obj (op V)) :
    canonicalMap F V' ((colimit.ι (presheafSystem F) j).app (op V')
      (((presheafSystem F).obj j).map (homOfLE hle).op τ)) =
    (colimitSheaf F).obj.map (homOfLE hle).op
      (canonicalMap F V ((colimit.ι (presheafSystem F) j).app (op V) τ)) :=
  (congr_arg (canonicalMap F V')
    (ConcreteCategory.congr_hom ((colimit.ι (presheafSystem F) j).naturality (homOfLE hle).op)
      τ)).trans
    (ConcreteCategory.congr_hom
      (NatTrans.naturality (Presheaf.toSheafify (colimitPresheaf F)) (homOfLE hle).op)
      ((colimit.ι (presheafSystem F) j).app (op V) τ))

/-- Uniqueness half of the sheaf condition for `(ℱ')^#`: two sections of the sheafification
over `U` that agree on every member of an open covering of `U` are equal. -/
lemma sheafify_eq_of_local_eq (U : Opens X) {ι : Type u} (W : ι → Opens X)
    (hWU : ∀ p, W p ≤ U) (hWcover : U ≤ ⨆ p, W p)
    (s t : (colimitSheaf F).obj.obj (op U))
    (hrestr : ∀ p, (colimitSheaf F).obj.map (homOfLE (hWU p)).op s =
                   (colimitSheaf F).obj.map (homOfLE (hWU p)).op t) :
    s = t := by
  have hUeq : U = ⨆ p, W p := le_antisymm hWcover (iSup_le hWU)
  subst hUeq
  exact Sheaf.eq_of_locally_eq (colimitSheaf F) W s t hrestr

/-- Evaluating the colimit isomorphism at `U` on the image of a section of `ℱₖ(U)` gives the
canonical coprojection. -/
private lemma colimitObjIso_hom_ι_apply (V : Opens X) (k : I)
    (x : ((presheafSystem F).obj k).obj (op V)) :
    (colimitObjIsoColimitCompEvaluation (presheafSystem F) (op V)).hom
      ((colimit.ι (presheafSystem F) k).app (op V) x) =
    colimit.ι (presheafSystem F ⋙ (evaluation _ _).obj (op V)) k x :=
  ConcreteCategory.congr_hom (colimitObjIsoColimitCompEvaluation_ι_app_hom (presheafSystem F) k
    (op V)) x

/-! ### Merging finitely many indices -/

variable [IsFiltered I]

omit [Small.{u} I] in
/-- Any finite family of morphisms out of a single object `k` of a filtered category factors
through one morphism out of `k`: there are `g : k ⟶ K` and morphisms `h i : t i ⟶ K` with
`a i ≫ h i = g` for every `i`. -/
lemma exists_common_factoring {ι : Type*} [Finite ι] {k : I} {t : ι → I} (a : ∀ i, k ⟶ t i) :
    ∃ (K : I) (g : k ⟶ K) (h : ∀ i, t i ⟶ K), ∀ i, a i ≫ h i = g := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  obtain ⟨S, hS⟩ := IsFiltered.sup_objs_exists
    (Finset.image (fun i ↦ Under.mk (a i)) (Finset.univ : Finset ι) : Finset (Under k))
  have f : ∀ i, Under.mk (a i) ⟶ S := fun i ↦
    (hS (Finset.mem_image_of_mem _ (Finset.mem_univ i))).some
  exact ⟨S.right, S.hom, fun i ↦ (f i).right, fun i ↦ Under.w (f i)⟩

/-- Any two sections of `ℱ'` over `U` are simultaneously represented at a single index. -/
lemma exists_common_index (U : Opens X) (s t : (colimitPresheaf F).obj (op U)) :
    ∃ (k : I) (sk tk : ((presheafSystem F).obj k).obj (op U)),
      (colimit.ι (presheafSystem F) k).app (op U) sk = s ∧
      (colimit.ι (presheafSystem F) k).app (op U) tk = t := by
  set iso := colimitObjIsoColimitCompEvaluation (presheafSystem F) (op U)
  obtain ⟨k, sk, tk, hsk, htk⟩ :=
    Types.FilteredColimit.jointly_surjective_of_isColimit₂
      (colimit.isColimit (presheafSystem F ⋙ (evaluation _ _).obj (op U))) (iso.hom s) (iso.hom t)
  exact ⟨k, sk, tk, iso.toEquiv.injective ((colimitObjIso_hom_ι_apply F U k sk).trans hsk),
    iso.toEquiv.injective ((colimitObjIso_hom_ι_apply F U k tk).trans htk)⟩

/-- Two sections of `ℱₖ(V)` have the same image in `ℱ'(V) = colimᵢ ℱᵢ(V)` if and only if
some transition map out of `k` already identifies them. -/
lemma colimit_eq_iff_eventual (V : Opens X) (k : I)
    (sk tk : ((presheafSystem F).obj k).obj (op V)) :
    (colimit.ι (presheafSystem F) k).app (op V) sk =
    (colimit.ι (presheafSystem F) k).app (op V) tk ↔
    ∃ (k' : I) (f : k ⟶ k'),
      ((presheafSystem F).map f).app (op V) sk =
      ((presheafSystem F).map f).app (op V) tk := by
  constructor
  · intro h
    exact (Types.FilteredColimit.isColimit_eq_iff'
      (colimit.isColimit (presheafSystem F ⋙ (evaluation _ _).obj (op V))) sk tk).mp
      ((colimitObjIso_hom_ι_apply F V k sk).symm.trans
        ((congr_arg (colimitObjIsoColimitCompEvaluation (presheafSystem F) (op V)).hom h).trans
          (colimitObjIso_hom_ι_apply F V k tk)))
  · rintro ⟨k', f, heq⟩
    have w := fun x ↦ ConcreteCategory.congr_hom
      (NatTrans.congr_app (colimit.w (presheafSystem F) f) (op V)) x
    exact (w sk).symm.trans ((congr_arg ((colimit.ι (presheafSystem F) k').app (op V)) heq).trans
      (w tk))

/-- Finitely many sections of `ℱ'`, one over each member of a finite family of opens, are all
represented at a single index of the system. -/
lemma exists_common_index_family {ι : Type*} [Finite ι] (W : ι → Opens X)
    (s : ∀ p, (colimitPresheaf F).obj (op (W p))) :
    ∃ (j : I) (sec : ∀ p, ((presheafSystem F).obj j).obj (op (W p))),
      ∀ p, (colimit.ι (presheafSystem F) j).app (op (W p)) (sec p) = s p := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  have hrep : ∀ p, ∃ (i : I) (x : ((presheafSystem F).obj i).obj (op (W p))),
      (colimit.ι (presheafSystem F) i).app (op (W p)) x = s p := by
    intro p
    obtain ⟨i, x, hx⟩ := Types.jointly_surjective_of_isColimit
      (colimit.isColimit (evalSystem F (W p)))
      ((colimitObjIsoColimitCompEvaluation (presheafSystem F) (op (W p))).hom (s p))
    exact ⟨i, x,
      (colimitObjIsoColimitCompEvaluation (presheafSystem F) (op (W p))).toEquiv.injective
        ((colimitObjIso_hom_ι_apply F (W p) i x).trans hx)⟩
  choose idx sec hsec using hrep
  obtain ⟨j, hj⟩ := IsFiltered.sup_objs_exists (Finset.image idx (Finset.univ : Finset ι))
  exact ⟨j, fun p ↦ ((presheafSystem F).map
    (hj (Finset.mem_image_of_mem _ (Finset.mem_univ p))).some).app (op (W p)) (sec p),
    fun p ↦ (ConcreteCategory.congr_hom
    (NatTrans.congr_app (colimit.w (presheafSystem F)
      (hj (Finset.mem_image_of_mem _ (Finset.mem_univ p))).some) (op (W p))) (sec p)).trans
      (hsec p)⟩

/-- If two sections of `ℱₖ(U)` have the same germ at a point `x ∈ U` after passing to `ℱ'`,
then they already agree on some open neighbourhood of `x` inside `U` after applying a single
transition map out of `k`. -/
lemma germ_eq_implies_local_eq (U : Opens X)
    (k : I) (sk tk : ((presheafSystem F).obj k).obj (op U))
    (x : X) (hx : x ∈ U)
    (heq : (colimitPresheaf F).germ U x hx
        ((colimit.ι (presheafSystem F) k).app (op U) sk) =
      (colimitPresheaf F).germ U x hx
        ((colimit.ι (presheafSystem F) k).app (op U) tk)) :
    ∃ (V : Opens X) (_ : x ∈ V) (hVU : V ≤ U) (k' : I) (g : k ⟶ k'),
      ((presheafSystem F).map g).app (op V)
        (((presheafSystem F).obj k).map (homOfLE hVU).op sk) =
      ((presheafSystem F).map g).app (op V)
        (((presheafSystem F).obj k).map (homOfLE hVU).op tk) := by
  obtain ⟨W, hxW, iU, iV, hW⟩ := Presheaf.germ_eq (colimitPresheaf F) x hx hx
    ((colimit.ι (presheafSystem F) k).app (op U) sk)
    ((colimit.ι (presheafSystem F) k).app (op U) tk) heq
  have hiUV : iU = iV := Subsingleton.elim _ _
  subst hiUV
  have nat_s := ConcreteCategory.congr_hom
    (NatTrans.naturality (colimit.ι (presheafSystem F) k) iU.op) sk
  have nat_t := ConcreteCategory.congr_hom
    (NatTrans.naturality (colimit.ι (presheafSystem F) k) iU.op) tk
  simp only [types_comp_apply] at nat_s nat_t
  have hW' : (colimit.ι (presheafSystem F) k).app (op W)
      (((presheafSystem F).obj k).map iU.op sk) =
    (colimit.ι (presheafSystem F) k).app (op W)
      (((presheafSystem F).obj k).map iU.op tk) := by
    rw [nat_s, nat_t]; exact hW
  obtain ⟨k', g, heq'⟩ := (colimit_eq_iff_eventual F W k _ _).mp hW'
  exact ⟨W, hxW, leOfHom iU, k', g, heq'⟩

/-- If finitely many pairs of sections over opens `V i` are each identified by some transition map
out of `k`, then a single transition map out of `k` identifies all of them. -/
private lemma exists_eventual_eq_family {I : Type v} [Category.{w} I] [IsFiltered I]
    (F : I ⥤ TopCat.Sheaf (Type u) X) {ι : Type*} [Finite ι] {k : I} (V : ι → Opens X)
    (a b : ∀ i, ((presheafSystem F).obj k).obj (op (V i)))
    (h : ∀ i, ∃ (k' : I) (g : k ⟶ k'),
      ((presheafSystem F).map g).app (op (V i)) (a i) =
      ((presheafSystem F).map g).app (op (V i)) (b i)) :
    ∃ (K : I) (γ : k ⟶ K), ∀ i, ((presheafSystem F).map γ).app (op (V i)) (a i) =
      ((presheafSystem F).map γ).app (op (V i)) (b i) := by
  choose k' g hg using h
  obtain ⟨K, γ, h', hfact⟩ := exists_common_factoring g
  exact ⟨K, γ, fun i ↦ by simp [← hfact i, hg i]⟩

/-- Two sections of `ℱₖ(U)` that are identified by a transition map out of `k` on each member of a
finite open covering of `U` are identified by a single transition map out of `k`. -/
private lemma exists_eventual_eq_of_cover {I : Type v} [Category.{w} I] [IsFiltered I]
    (F : I ⥤ TopCat.Sheaf (Type u) X) {ι : Type u} [Finite ι] (k : I) (U : Opens X)
    (sk tk : ((presheafSystem F).obj k).obj (op U)) (W : ι → Opens X) (hWU : ∀ p, W p ≤ U)
    (hWcover : U ≤ ⨆ p, W p)
    (hloc : ∀ p, ∃ (k' : I) (g : k ⟶ k'),
      ((presheafSystem F).map g).app (op (W p))
        (((presheafSystem F).obj k).map (homOfLE (hWU p)).op sk) =
      ((presheafSystem F).map g).app (op (W p))
        (((presheafSystem F).obj k).map (homOfLE (hWU p)).op tk)) :
    ∃ (k' : I) (g : k ⟶ k'),
      ((presheafSystem F).map g).app (op U) sk = ((presheafSystem F).map g).app (op U) tk := by
  obtain ⟨K, γ, hγ⟩ := exists_eventual_eq_family F W _ _ hloc
  refine ⟨K, γ, sheaf_eq_of_local_eq F K U W hWU hWcover _ _ fun p ↦ ?_⟩
  rw [map_restrict_app_eq, map_restrict_app_eq]
  exact hγ p

/-- The injectivity of `Ψ` at `U` can be checked on sections coming from a single index: it
suffices that equal images in `(ℱ')^#(U)` are identified by some transition map. -/
private lemma injective_canonicalMap_of_eventual (U : Opens X)
    (h : ∀ (k : I) (sk tk : ((presheafSystem F).obj k).obj (op U)),
      canonicalMap F U ((colimit.ι (presheafSystem F) k).app (op U) sk) =
      canonicalMap F U ((colimit.ι (presheafSystem F) k).app (op U) tk) →
      ∃ (k' : I) (g : k ⟶ k'),
        ((presheafSystem F).map g).app (op U) sk = ((presheafSystem F).map g).app (op U) tk) :
    Function.Injective (canonicalMap F U) := by
  intro s t hst
  obtain ⟨k, sk, tk, rfl, rfl⟩ := exists_common_index F U s t
  obtain ⟨k', g, heq⟩ := h k sk tk hst
  exact (colimit_eq_iff_eventual F U k sk tk).mpr ⟨k', g, heq⟩

/-- A quasi-compact open `U`, with an open neighbourhood `V x hx` of each of its points `x`, is
covered by finitely many of these neighbourhoods. -/
private lemma exists_finset_cover_of_isCompact (U : Opens X) (hU : IsCompact (U : Set X))
    (V : ∀ x, x ∈ U → Opens X) (hxV : ∀ x hx, x ∈ V x hx) :
    ∃ s : Finset ↥U, U ≤ ⨆ p : ↥s, V p.1.1 p.1.2 := by
  obtain ⟨s, hs⟩ := hU.elim_finite_subcover (fun p : ↥U ↦ (V p.1 p.2 : Set X))
    (fun p ↦ (V p.1 p.2).isOpen) fun x hx ↦ Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxV x hx⟩
  refine ⟨s, fun x hx ↦ ?_⟩
  obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp (hs hx)
  exact Opens.mem_iSup.mpr ⟨⟨p, hp⟩, hxp⟩

/-- If `σ` is, on each member of a finite open covering of `U` with pairwise injective `Ψ`, the
image of a section of `ℱ'`, then `σ` is in the image of `Ψ`. -/
private lemma exists_canonicalMap_eq_of_cover {K : Type u} [Finite K] (U : Opens X)
    (σ : (colimitSheaf F).obj.obj (op U)) (W : K → Opens X) (hWU : ∀ p, W p ≤ U)
    (hWcover : U ≤ ⨆ p, W p) (hinj : ∀ p q, Function.Injective (canonicalMap F (W p ⊓ W q)))
    (s_W : ∀ p, (colimitPresheaf F).obj (op (W p)))
    (hs_W : ∀ p, canonicalMap F (W p) (s_W p) =
      (colimitSheaf F).obj.map (homOfLE (hWU p)).op σ) :
    ∃ s, canonicalMap F U s = σ := by
  obtain ⟨j, τ, hτ⟩ := exists_common_index_family F W s_W
  have hrestr : ∀ (p : K) (V : Opens X) (hle : V ≤ W p),
      canonicalMap F V ((colimit.ι (presheafSystem F) j).app (op V)
        (((presheafSystem F).obj j).map (homOfLE hle).op (τ p))) =
      (colimitSheaf F).obj.map (homOfLE (hle.trans (hWU p))).op σ := by
    intro p V hle
    rw [canonicalMap_ι_restrict, hτ p, hs_W p, ← Functor.map_comp_apply]
    rfl
  have hoverlap : ∀ r : K × K, ∃ (m : I) (e : j ⟶ m),
      ((presheafSystem F).map e).app (op (W r.1 ⊓ W r.2))
        (((presheafSystem F).obj j).map (homOfLE inf_le_left).op (τ r.1)) =
      ((presheafSystem F).map e).app (op (W r.1 ⊓ W r.2))
        (((presheafSystem F).obj j).map (homOfLE inf_le_right).op (τ r.2)) := fun r ↦
    (colimit_eq_iff_eventual F (W r.1 ⊓ W r.2) j _ _).mp
      (hinj r.1 r.2 ((hrestr r.1 _ inf_le_left).trans (hrestr r.2 _ inf_le_right).symm))
  obtain ⟨M, γ, hγ⟩ := exists_eventual_eq_family F (fun r : K × K ↦ W r.1 ⊓ W r.2)
    (fun r ↦ ((presheafSystem F).obj j).map (homOfLE inf_le_left).op (τ r.1))
    (fun r ↦ ((presheafSystem F).obj j).map (homOfLE inf_le_right).op (τ r.2)) hoverlap
  obtain ⟨s_M, hs_M⟩ := sheaf_glue F M U W hWU hWcover
    (fun p ↦ ((presheafSystem F).map γ).app (op (W p)) (τ p)) fun p q ↦ by
      rw [map_restrict_app_eq, map_restrict_app_eq]
      exact hγ (p, q)
  refine ⟨(colimit.ι (presheafSystem F) M).app (op U) s_M,
    sheafify_eq_of_local_eq F U W hWU hWcover _ _ fun p ↦ ?_⟩
  rw [← canonicalMap_ι_restrict F M U (W p) (hWU p) s_M, hs_M p]
  have hw : (colimit.ι (presheafSystem F) M).app (op (W p))
      (((presheafSystem F).map γ).app (op (W p)) (τ p)) =
      (colimit.ι (presheafSystem F) j).app (op (W p)) (τ p) :=
    ConcreteCategory.congr_hom
      (NatTrans.congr_app (colimit.w (presheafSystem F) γ) (op (W p))) (τ p)
  rw [hw, hτ p, hs_W p]

/-! ### Injectivity and bijectivity of the canonical map -/

/-- If all the transition maps are injective, then `Ψ` is injective for any open `U`. -/
@[stacks 009F]
theorem injective_canonicalMap_of_hasInjectiveTransitions
    (hInj : HasInjectiveTransitions F) (U : Opens X) :
    Function.Injective (canonicalMap F U) := by
  refine injective_canonicalMap_of_eventual F U fun k sk tk hst ↦ ?_
  have hgerm := (canonicalMap_eq_iff F U _ _).mp hst
  have hlocal : ∀ (p : U), ∃ (V : Opens X) (_ : (p : X) ∈ V) (hVU : V ≤ U),
      ((presheafSystem F).obj k).map (homOfLE hVU).op sk =
      ((presheafSystem F).obj k).map (homOfLE hVU).op tk := by
    intro ⟨x, hx⟩
    obtain ⟨V, hxV, hVU, k', g, heq'⟩ :=
      germ_eq_implies_local_eq F U k sk tk x hx (hgerm x hx)
    exact ⟨V, hxV, hVU, hInj g V heq'⟩
  choose Vfun hVmem hVle hVeq using hlocal
  refine ⟨k, 𝟙 k, ?_⟩
  rw [sheaf_eq_of_local_eq F k U Vfun hVle (fun x hx ↦
    show x ∈ (⨆ j, Vfun j) from
      Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hVmem ⟨x, hx⟩⟩) sk tk hVeq]

/-- If `U` is quasi-compact, then `Ψ` is injective, with no hypothesis on the transition
maps. -/
@[stacks 009F]
theorem injective_canonicalMap_of_isCompact (U : Opens X)
    (hU : IsCompact (U : Set X)) :
    Function.Injective (canonicalMap F U) := by
  refine injective_canonicalMap_of_eventual F U fun k sk tk hst ↦ ?_
  have hgerm := (canonicalMap_eq_iff F U _ _).mp hst
  choose V hxV hVU k' g heqV using fun x hx ↦
    germ_eq_implies_local_eq F U k sk tk x hx (hgerm x hx)
  obtain ⟨s, hs⟩ := exists_finset_cover_of_isCompact U hU V hxV
  exact exists_eventual_eq_of_cover F k U sk tk (fun p : ↥s ↦ V p.1.1 p.1.2)
    (fun p ↦ hVU _ _) hs fun p ↦ ⟨k' _ _, g _ _, heqV _ _⟩

/-- If `U` is quasi-compact and all the transition maps are injective, then `Ψ` is
bijective. -/
@[stacks 009F]
theorem bijective_canonicalMap_of_isCompact_of_hasInjectiveTransitions
    (hInj : HasInjectiveTransitions F) (U : Opens X)
    (hU : IsCompact (U : Set X)) :
    Function.Bijective (canonicalMap F U) := by
  refine ⟨injective_canonicalMap_of_isCompact F U hU, fun σ ↦ ?_⟩
  choose V hxV hVU s_loc hs_loc using exists_localPreimage F U σ
  obtain ⟨s, hs⟩ := exists_finset_cover_of_isCompact U hU V hxV
  exact exists_canonicalMap_eq_of_cover F U σ (fun p : ↥s ↦ V p.1.1 p.1.2) (fun p ↦ hVU _ _) hs
    (fun _ _ ↦ injective_canonicalMap_of_hasInjectiveTransitions F hInj _)
    (fun p ↦ s_loc _ _) fun p ↦ hs_loc _ _

/-- If `U` has a cofinal system of finite open coverings whose pairwise intersections are
quasi-compact, then `Ψ` is bijective, with no hypothesis on the transition maps. -/
@[stacks 009F, sga "4 VI 1.23" "topological space case"]
theorem bijective_canonicalMap_of_hasFiniteCompactCofinalCovers (U : Opens X)
    (hU : HasFiniteCompactCofinalCovers (X := X) U) :
    Function.Bijective (canonicalMap F U) := by
  refine ⟨?_, fun σ ↦ ?_⟩
  · refine injective_canonicalMap_of_eventual F U fun k sk tk hst ↦ ?_
    obtain ⟨K, _, W, hWU, hWcover, -, hWQC⟩ :=
      hU (fun (_ : PUnit.{u+1}) ↦ U) (fun _ ↦ le_refl U) (by simp)
    refine exists_eventual_eq_of_cover F k U sk tk W hWU hWcover fun κ ↦
      exists_eventual_eq_of_cover F k (W κ) _ _ (fun κ' ↦ W κ ⊓ W κ') (fun _ ↦ inf_le_left)
        (by rw [← inf_iSup_eq]; exact le_inf le_rfl ((hWU κ).trans hWcover)) fun κ' ↦
        (colimit_eq_iff_eventual F _ k _ _).mp
          (injective_canonicalMap_of_isCompact F _ (hWQC κ κ') ?_)
    simp only [canonicalMap_ι_restrict, hst]
  · choose V hxV hVU s_loc hs_loc using exists_localPreimage F U σ
    obtain ⟨K, _, W, hWU, hWcover, hrefine, hWQC⟩ :=
      hU (fun (p : U) ↦ V p.1 p.2) (fun p ↦ hVU p.1 p.2)
        (fun x hx ↦ Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV x hx⟩)
    choose ref_idx hW_le_V using hrefine
    refine exists_canonicalMap_eq_of_cover F U σ W hWU hWcover
      (fun κ κ' ↦ injective_canonicalMap_of_isCompact F _ (hWQC κ κ'))
      (fun κ ↦ (colimitPresheaf F).map (homOfLE (hW_le_V κ)).op
        (s_loc (ref_idx κ).1 (ref_idx κ).2)) fun κ ↦ ?_
    have nat := ConcreteCategory.congr_hom
      (NatTrans.naturality (Presheaf.toSheafify (colimitPresheaf F))
        (homOfLE (hW_le_V κ)).op) (s_loc (ref_idx κ).1 (ref_idx κ).2)
    refine nat.trans ((congr_arg ((colimitSheaf F).obj.map (homOfLE (hW_le_V κ)).op)
      (hs_loc _ _)).trans ?_)
    rw [← Functor.map_comp_apply]
    rfl

/-! ### Specialisation to a directed preorder -/

section DirectedPreorder

variable {I : Type v} [Preorder I] (F : I ⥤ TopCat.Sheaf (Type u) X)

/-- For a system indexed by a directed preorder, the transition maps are injective as soon as
the maps `(presheafSystem F).map (homOfLE h)` are. -/
lemma hasInjectiveTransitions_of_le
    (h : ∀ ⦃i i' : I⦄ (hle : i ≤ i') (V : Opens X),
      Function.Injective (((presheafSystem F).map (homOfLE hle)).app (op V))) :
    HasInjectiveTransitions F := by
  intro i i' f V
  obtain ⟨⟨hle⟩⟩ := f
  exact h hle V

end DirectedPreorder

end DirectedColimitOfSheaves
