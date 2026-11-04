module

public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sheaves on a basis for a topological space (Stacks 009O)

Let `X` be a topological space and let `B : Set (Opens X)` be a basis for its
topology. Regarding `B` as the full subcategory `BasisCat B` of `Opens X` cut out
by membership in `B`, a *presheaf on `B`* is a functor `(BasisCat B)ᵒᵖ ⥤ Type u`,
and such a presheaf is a *sheaf on `B`* when it satisfies the gluing axiom for
coverings of a basis element by basis elements.

The sheaf condition on a basis is spelled out here as the conjunction of a
*separated* and a *gluing* clause (`IsSheafOnBasis`) rather than as an equalizer
diagram. The two are equivalent, and the split form is what the covering
arguments below actually consume: every step either identifies two sections that
agree on a basis cover, or glues a compatible family indexed by a basis cover.
Note that the compatibility required by `IsSheafOnBasis.glue` is indexed by
*basis elements* `V` contained in `Uᵢ ⊓ Uⱼ`, not by the intersection itself,
which need not lie in `B`; this is exactly the equalizer condition of the source.

Restricting a presheaf on `X` along the inclusion `BasisCat B ⥤ Opens X` sends
sheaves to sheaves (`isSheafOnBasis_restrict`), giving the restriction functor
`restrictFunctor : TopCat.Sheaf (Type u) X ⥤ SheafOnBasis B`. The main result is
that this functor is an equivalence of categories: it is faithful and full by
locality of sections, and essentially surjective because a sheaf on `B` extends
to `X` by the presheaf of compatible families of its sections over the basis
elements contained in a given open.
-/

@[expose] public section

namespace Stacks.OpensBasis

open CategoryTheory TopologicalSpace Opposite

universe u

variable {X : TopCat.{u}} (B : Set (Opens X))

/-- The basis `B` as an `ObjectProperty` of `Opens X`. -/
@[implicit_reducible]
def basisProp : ObjectProperty (Opens X) := fun U => U ∈ B

/-- The basis `B` as a (full sub)category of `Opens X`. -/
abbrev BasisCat : Type u := (basisProp B).FullSubcategory

/-- The fully faithful inclusion functor of `BasisCat B` into `Opens X`. -/
@[implicit_reducible]
def basisInclusion : BasisCat B ⥤ Opens X := (basisProp B).ι

/-- The morphism `V ⟶ U` in `BasisCat B` coming from `V.obj ≤ U.obj`. -/
@[implicit_reducible]
def basisHom {U V : BasisCat B} (h : V.obj ≤ U.obj) : V ⟶ U :=
  ObjectProperty.homMk (CategoryTheory.homOfLE h)

/-- A presheaf of sets on the basis `B`. -/
abbrev PresheafOnBasis : Type (u + 1) := (BasisCat B)ᵒᵖ ⥤ Type u

/-- The restriction map of a presheaf on a basis, along an inclusion of basis
elements. -/
@[implicit_reducible]
def PresheafOnBasis.restrictMap (F : PresheafOnBasis B)
    {U V : BasisCat B} (h : V.obj ≤ U.obj) (s : F.obj (op U)) : F.obj (op V) :=
  F.map (basisHom B h).op s

/-- The sheaf condition for a presheaf on the basis `B`, in the "separated +
gluing" form equivalent to the equalizer condition. -/
@[ega "0 3.2.2"]
structure IsSheafOnBasis (F : PresheafOnBasis B) : Prop where
  /-- Separated condition: a section is determined by its restrictions to a
  cover by basis elements. -/
  separated :
    ∀ (U : BasisCat B) {ι : Type u} (𝒰 : ι → BasisCat B)
      (hcov : ⨆ i, ((𝒰 i).obj : Opens X) = U.obj)
      (s t : F.obj (op U)),
      (∀ i, F.restrictMap B
              ((le_iSup (fun j => ((𝒰 j).obj : Opens X)) i).trans_eq hcov) s
            = F.restrictMap B
              ((le_iSup (fun j => ((𝒰 j).obj : Opens X)) i).trans_eq hcov) t)
      → s = t
  /-- Gluing condition: a compatible family of sections over a cover by basis
  elements glues to a section. -/
  glue :
    ∀ (U : BasisCat B) {ι : Type u} (𝒰 : ι → BasisCat B)
      (hcov : ⨆ i, ((𝒰 i).obj : Opens X) = U.obj)
      (s : ∀ i, F.obj (op (𝒰 i)))
      (_ :
        ∀ i j (V : BasisCat B)
          (hVi : V.obj ≤ (𝒰 i).obj) (hVj : V.obj ≤ (𝒰 j).obj),
          F.restrictMap B hVi (s i) = F.restrictMap B hVj (s j)),
      ∃ t : F.obj (op U),
        ∀ i, F.restrictMap B
                ((le_iSup (fun j => ((𝒰 j).obj : Opens X)) i).trans_eq hcov) t
              = s i

/-- The `ObjectProperty` on presheaves on the basis `B` of being a sheaf. -/
@[implicit_reducible]
def isSheafOnBasisProp : ObjectProperty (PresheafOnBasis B) := fun F => IsSheafOnBasis B F

/-- The category of sheaves of sets on the basis `B`. Its objects are presheaves
on `B` satisfying the sheaf condition, and morphisms are natural transformations
of underlying presheaves. -/
@[ega "0 3.2.2"]
abbrev SheafOnBasis : Type (u + 1) := (isSheafOnBasisProp B).FullSubcategory

/-- Restriction of a presheaf on `X` to the basis `B`: precompose with the
(opposite of the) inclusion functor. -/
@[implicit_reducible]
def restrictPresheafFunctor :
    ((Opens X)ᵒᵖ ⥤ Type u) ⥤ PresheafOnBasis B :=
  (Functor.whiskeringLeft _ _ _).obj (basisInclusion B).op

/-- Restriction of a sheaf on `X` to a presheaf on `B`. -/
@[implicit_reducible]
def restrictOfSheaf (F : TopCat.Sheaf (Type u) X) : PresheafOnBasis B :=
  (restrictPresheafFunctor B).obj F.1

lemma PresheafOnBasis.restrictMap_apply (F : PresheafOnBasis B) {U V : BasisCat B}
    (h : V.obj ≤ U.obj) (s : F.obj (op U)) : F.restrictMap B h s = F.map (basisHom B h).op s :=
  rfl

lemma restrictOfSheaf_restrictMap (F : TopCat.Sheaf (Type u) X) {U V : BasisCat B}
    (h : V.obj ≤ U.obj) (s : (restrictOfSheaf B F).obj (op U)) :
    (restrictOfSheaf B F).restrictMap B h s = F.1.map (homOfLE h).op s :=
  rfl

/-- The hom-sets of `Opens X` are subsingletons, so the restriction maps of a
presheaf on `X` along two morphisms with the same source and target agree. -/
private lemma map_congr_of_hom_eq (F : (Opens X)ᵒᵖ ⥤ Type u) {A C : (Opens X)ᵒᵖ}
    (f g : A ⟶ C) (x : F.obj A) : F.map f x = F.map g x := by
  rw [Subsingleton.elim f g]

/-- The hom-sets of `BasisCat B` are subsingletons too, so the restriction maps of
a presheaf on `B` along two morphisms with the same source and target agree. -/
private lemma basisMap_congr_of_hom_eq (F : PresheafOnBasis B) {A C : (BasisCat B)ᵒᵖ}
    (f g : A ⟶ C) (x : F.obj A) : F.map f x = F.map g x := by
  rw [show f = g from Quiver.Hom.unop_inj
    (ObjectProperty.hom_ext _ (Subsingleton.elim _ _))]

/-- The sheaf condition of a sheaf on `X` in "unique gluing" form. -/
lemma sheaf_unique_gluing (F : TopCat.Sheaf (Type u) X) :
    TopCat.Presheaf.IsSheafUniqueGluing F.1 :=
  (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types F.1).mp F.2

private lemma sheaf_eq_of_locally_eq (F : TopCat.Sheaf (Type u) X)
    {ι : Type u} (V : ι → Opens X)
    (a b : F.1.obj (op (⨆ i, V i)))
    (h : ∀ i, F.1.map (Opens.leSupr V i).op a = F.1.map (Opens.leSupr V i).op b) :
    a = b := by
  have hsheaf := sheaf_unique_gluing F
  let sf : (i : ι) → F.1.obj (op (V i)) := fun i => F.1.map (Opens.leSupr V i).op a
  have hcompat_sf : TopCat.Presheaf.IsCompatible F.1 V sf := by
    intro i' j'
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
    congr 1
  have ha_glue : TopCat.Presheaf.IsGluing F.1 V sf a := fun i' => rfl
  have hb_glue : TopCat.Presheaf.IsGluing F.1 V sf b := fun i' => (h i').symm
  exact (hsheaf V sf hcompat_sf).unique ha_glue hb_glue

private lemma sheaf_eq_of_cover (F : TopCat.Sheaf (Type u) X)
    {ι : Type u} (V : ι → Opens X) (W : Opens X)
    (hcov : ⨆ i, V i = W)
    (a b : F.1.obj (op W))
    (h : ∀ i, F.1.map ((le_iSup V i).trans_eq hcov).hom.op a =
              F.1.map ((le_iSup V i).trans_eq hcov).hom.op b) :
    a = b := by
  subst hcov
  exact sheaf_eq_of_locally_eq F V a b h

/-- Every point `p` of an open `W` has a basis element inside a given neighbourhood `A p ≤ W`
of it, and these basis elements cover `W`. -/
private lemma exists_basis_cover (hB : Opens.IsBasis B) (W : Opens X) (A : ↑W → Opens X)
    (hA : ∀ p, (p : X) ∈ A p) (hAW : ∀ p, A p ≤ W) :
    ∃ Vf : ↑W → Opens X, (∀ p, Vf p ∈ B) ∧ (∀ p, Vf p ≤ A p) ∧ ⨆ p, Vf p = W := by
  choose Vf hVfB hxVf hVfle using fun p : ↑W =>
    Opens.isBasis_iff_nbhd.mp hB (U := A p) (x := p.1) (hA p)
  exact ⟨Vf, hVfB, hVfle, le_antisymm (iSup_le fun p => (hVfle p).trans (hAW p))
    fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxVf ⟨x, hx⟩⟩⟩

/-- An open `V` contained in a union `⨆ i, A i` is covered by basis elements, each
contained in `V` and in some `A (j p)`. -/
private lemma exists_basis_cover_subordinate (hB : Opens.IsBasis B) {ι : Type*} (V : Opens X)
    (A : ι → Opens X) (hV : V ≤ ⨆ i, A i) :
    ∃ (j : ↑V → ι) (Z : ↑V → BasisCat B), (∀ p, (Z p).obj ≤ V) ∧
      (∀ p, (Z p).obj ≤ A (j p)) ∧ ⨆ p, (Z p).obj = V := by
  choose j hj using fun p : ↑V => Opens.mem_iSup.mp (hV p.2)
  obtain ⟨Vf, hVfB, hVfle, hcov⟩ := exists_basis_cover B hB V (fun p => V ⊓ A (j p))
    (fun p => ⟨p.2, hj p⟩) fun _ => inf_le_left
  exact ⟨j, fun p => ⟨Vf p, hVfB p⟩, fun p => (hVfle p).trans inf_le_left,
    fun p => (hVfle p).trans inf_le_right, hcov⟩

/-- The separated clause of the sheaf condition for the restriction of a sheaf on
`X` to the basis `B`: two sections over a basis element that agree on a basis
cover of it are equal. -/
private lemma isSheafOnBasis_restrict_separated (F : TopCat.Sheaf (Type u) X)
    (U : BasisCat B) {ι : Type u} (𝒰 : ι → BasisCat B)
    (hcov : ⨆ i, ((𝒰 i).obj : Opens X) = U.obj)
    (s t : (restrictOfSheaf B F).obj (op U))
    (hagree : ∀ i, (restrictOfSheaf B F).restrictMap B
              ((le_iSup (fun j => ((𝒰 j).obj : Opens X)) i).trans_eq hcov) s
            = (restrictOfSheaf B F).restrictMap B
              ((le_iSup (fun j => ((𝒰 j).obj : Opens X)) i).trans_eq hcov) t) :
    s = t :=
  sheaf_eq_of_cover F (fun i => (𝒰 i).obj) U.obj hcov s t hagree

/-- The gluing clause of the sheaf condition for the restriction of a sheaf on
`X` to the basis `B`: a family of sections over a basis cover that is
compatible on all basis elements inside the pairwise intersections glues. -/
private lemma isSheafOnBasis_restrict_glue (hB : Opens.IsBasis B) (F : TopCat.Sheaf (Type u) X)
    (U : BasisCat B) {ι : Type u} (𝒰 : ι → BasisCat B)
    (hcov : ⨆ i, ((𝒰 i).obj : Opens X) = U.obj)
    (s : ∀ i, (restrictOfSheaf B F).obj (op (𝒰 i)))
    (compat : ∀ i j (V : BasisCat B)
          (hVi : V.obj ≤ (𝒰 i).obj) (hVj : V.obj ≤ (𝒰 j).obj),
          (restrictOfSheaf B F).restrictMap B hVi (s i) =
            (restrictOfSheaf B F).restrictMap B hVj (s j)) :
    ∃ t : (restrictOfSheaf B F).obj (op U),
      ∀ i, (restrictOfSheaf B F).restrictMap B
              ((le_iSup (fun j => ((𝒰 j).obj : Opens X)) i).trans_eq hcov) t
            = s i := by
  let U' : ι → Opens X := fun i => (𝒰 i).obj
  have hcompat : TopCat.Presheaf.IsCompatible F.1 U' s := by
    intro i j
    obtain ⟨Vf, hVfB, hVfle, hVcov⟩ := exists_basis_cover B hB (U' i ⊓ U' j) (fun _ => U' i ⊓ U' j)
      (fun p => p.2) fun _ => le_rfl
    apply sheaf_eq_of_cover F Vf (U' i ⊓ U' j) hVcov
    intro p
    have hVi : Vf p ≤ (𝒰 i).obj := (hVfle p).trans inf_le_left
    have hVj : Vf p ≤ (𝒰 j).obj := (hVfle p).trans inf_le_right
    have hc : F.1.map hVi.hom.op (s i) = F.1.map hVj.hom.op (s j) :=
      compat i j ⟨Vf p, hVfB p⟩ hVi hVj
    simp only [← Functor.map_comp_apply]
    exact (map_congr_of_hom_eq F.1 _ hVi.hom.op (s i)).trans
      (hc.trans (map_congr_of_hom_eq F.1 hVj.hom.op _ (s j)))
  obtain ⟨t, ht, _⟩ := sheaf_unique_gluing F U' s hcompat
  have heq : (⨆ i, U' i) = U.obj := hcov
  refine ⟨F.1.map (eqToHom (congrArg op heq)) t, fun i => ?_⟩
  rw [restrictOfSheaf_restrictMap]
  rw [← Functor.map_comp_apply]
  exact (map_congr_of_hom_eq F.1 _ (Opens.leSupr U' i).op t).trans (ht i)

/-- Restricting a sheaf on `X` along the inclusion of the basis `B` gives a
sheaf on `B`. -/
theorem isSheafOnBasis_restrict (hB : Opens.IsBasis B) (F : TopCat.Sheaf (Type u) X) :
    IsSheafOnBasis B (restrictOfSheaf B F) :=
  ⟨isSheafOnBasis_restrict_separated B F, isSheafOnBasis_restrict_glue B hB F⟩

/-- **Stacks 009O.** The restriction-to-basis functor
`r : Sh(X) ⥤ Sh(B)`, sending a sheaf on `X` to its restriction to the basis
elements. -/
@[stacks 009O, implicit_reducible]
noncomputable def restrictFunctor (hB : Opens.IsBasis B) : TopCat.Sheaf (Type u) X ⥤ SheafOnBasis B
    :=
  (isSheafOnBasisProp B).lift
    (TopCat.Sheaf.forget (Type u) X ⋙ restrictPresheafFunctor B)
    (fun F => isSheafOnBasis_restrict B hB F)

-- The proofs of faithfulness, fullness and essential surjectivity all read a
-- morphism of sheaves on `B` as a morphism of the restricted presheaves, which
-- needs Mathlib's plain `def` `TopCat.Sheaf.forget` to unfold at `implicit` transparency.
attribute [local implicit_reducible] TopCat.Sheaf.forget

/-- The restriction functor is faithful: a morphism of sheaves on `X` is
determined by its components at the basis elements, since every open is covered
by basis elements and sections of a sheaf are local. -/
private lemma restrictFunctor_faithful (hB : Opens.IsBasis B) :
    (restrictFunctor B hB).Faithful := by
  constructor
  intro F G f g h
  apply InducedCategory.Hom.ext
  apply NatTrans.ext
  funext U
  have hbasis : ∀ (V : BasisCat B), f.hom.app (op V.obj) = g.hom.app (op V.obj) := by
    intro V
    have h' := congrArg InducedCategory.Hom.hom h
    have h'' : ((restrictFunctor B hB).map f).hom.app (op V) =
               ((restrictFunctor B hB).map g).hom.app (op V) := by
      rw [h']
    simp only [restrictFunctor, ObjectProperty.lift_map] at h''
    exact h''
  apply ConcreteCategory.hom_ext
  intro s
  obtain ⟨Vf, hVfB, -, hcov⟩ := exists_basis_cover B hB U.unop (fun _ => U.unop) (fun p => p.2)
    fun _ => le_rfl
  apply sheaf_eq_of_cover G Vf U.unop hcov
  intro p
  conv_lhs => rw [show f.hom.app U s = f.hom.app (op (U.unop)) s from rfl]
  conv_rhs => rw [show g.hom.app U s = g.hom.app (op (U.unop)) s from rfl]
  rw [← NatTrans.naturality_apply f.hom ((le_iSup Vf p).trans_eq hcov).hom.op s]
  rw [← NatTrans.naturality_apply g.hom ((le_iSup Vf p).trans_eq hcov).hom.op s]
  exact ConcreteCategory.congr_hom (hbasis ⟨Vf p, hVfB p⟩) (F.1.map ((le_iSup Vf p).trans_eq
      hcov).hom.op s)

/-- Naturality of a natural transformation between restricted presheaves, read at
the level of `Opens X`. -/
private lemma nat_on_basis (F G : TopCat.Sheaf (Type u) X)
    (η : (restrictPresheafFunctor B).obj F.1 ⟶ (restrictPresheafFunctor B).obj G.1)
    (V : Opens X) (hVB : V ∈ B) (W : Opens X) (hWB : W ∈ B)
    (h : W ≤ V) (x : F.1.obj (op V)) :
    η.app (op ⟨W, hWB⟩) (F.1.map h.hom.op x) = G.1.map h.hom.op (η.app (op ⟨V, hVB⟩) x) :=
  NatTrans.naturality_apply η (basisHom (U := ⟨V, hVB⟩) (V := ⟨W, hWB⟩) B h).op x

/-- The images under `η` of the restrictions of a section `s` over `U` to a basis
cover of `U` form a compatible family. -/
private lemma full_compat (hB : Opens.IsBasis B) (F G : TopCat.Sheaf (Type u) X)
    (η : (restrictPresheafFunctor B).obj F.1 ⟶ (restrictPresheafFunctor B).obj G.1)
    (U : Opens X) (s : F.1.obj (op U))
    (Vf : ↑U → Opens X) (hVfB : ∀ p, Vf p ∈ B) (hVfle : ∀ p, Vf p ≤ U) :
    TopCat.Presheaf.IsCompatible G.1 Vf
      (fun p => η.app (op ⟨Vf p, hVfB p⟩) (F.1.map (hVfle p).hom.op s)) := by
  -- Cover each intersection Vf p ⊓ Vf q by basis elements; use nat_on_basis
  -- to show both sides reduce to η applied to the same restriction of s.
  intro p q
  obtain ⟨Wf, hWfB, hWfle, hWcov⟩ := exists_basis_cover B hB (Vf p ⊓ Vf q)
    (fun _ => Vf p ⊓ Vf q) (fun r => r.2) fun _ => le_rfl
  apply sheaf_eq_of_cover G Wf (Vf p ⊓ Vf q) hWcov
  intro r
  -- Pushing the `m`-component of `η` down to `Wf r` gives `η` of the restriction of `s`.
  have side : ∀ (m : Opens X) (hmB : m ∈ B) (hm : m ≤ U) (g : Vf p ⊓ Vf q ⟶ m) (hWm : Wf r ≤ m),
      G.1.map ((le_iSup Wf r).trans_eq hWcov).hom.op
        (G.1.map g.op (η.app (op ⟨m, hmB⟩) (F.1.map hm.hom.op s))) =
      η.app (op ⟨Wf r, hWfB r⟩) (F.1.map (hWm.trans hm).hom.op s) := by
    intro m hmB hm g hWm
    rw [← Functor.map_comp_apply, map_congr_of_hom_eq G.1 _ hWm.hom.op,
      ← nat_on_basis B F G η m hmB (Wf r) (hWfB r) hWm, ← Functor.map_comp_apply]
    congr 1
  exact (side _ (hVfB p) (hVfle p) _ ((hWfle r).trans inf_le_left)).trans
    (side _ (hVfB q) (hVfle q) _ ((hWfle r).trans inf_le_right)).symm

/-- Two maps that are both described on basis elements by `η` commute with the
restriction `G(U) ⟶ G(W)` along `W ≤ U`. -/
private lemma full_naturality (hB : Opens.IsBasis B) (F G : TopCat.Sheaf (Type u) X)
    (η : (restrictPresheafFunctor B).obj F.1 ⟶ (restrictPresheafFunctor B).obj G.1)
    (U W : Opens X) (i : W ≤ U) (s : F.1.obj (op U))
    -- The constructed section over U (glued from basis cover of U)
    (fU : F.1.obj (op U) → G.1.obj (op U))
    -- The constructed section over W (glued from basis cover of W)
    (fW : F.1.obj (op W) → G.1.obj (op W))
    (hfU : ∀ (V : Opens X) (hVB : V ∈ B) (hVU : V ≤ U),
      G.1.map hVU.hom.op (fU s) = η.app (op ⟨V, hVB⟩) (F.1.map hVU.hom.op s))
    (hfW : ∀ (V : Opens X) (hVB : V ∈ B) (hVW : V ≤ W),
      G.1.map hVW.hom.op (fW (F.1.map i.hom.op s)) = η.app (op ⟨V, hVB⟩) (F.1.map hVW.hom.op
          (F.1.map i.hom.op s))) :
    G.1.map i.hom.op (fU s) = fW (F.1.map i.hom.op s) := by
  -- Both sides agree on all basis elements V ≤ W by hfU, hfW + functoriality of F.1.map.
  -- Use sheaf_eq_of_cover G to conclude.
  obtain ⟨Vf, hVfB, hVfle, hVcov⟩ := exists_basis_cover B hB W (fun _ => W) (fun p => p.2)
    fun _ => le_rfl
  apply sheaf_eq_of_cover G Vf W hVcov
  intro p
  -- LHS: compose G maps then use hfU
  rw [← Functor.map_comp_apply]
  have lhs_eq : G.1.map (i.hom.op ≫ ((le_iSup Vf p).trans_eq hVcov).hom.op) (fU s) =
    G.1.map ((hVfle p).trans i).hom.op (fU s) := by congr 1
  rw [lhs_eq, hfU (Vf p) (hVfB p) ((hVfle p).trans i)]
  -- RHS: use hfW then compose F maps
  have rhs_eq : G.1.map ((le_iSup Vf p).trans_eq hVcov).hom.op (fW (F.1.map i.hom.op s)) =
    G.1.map (hVfle p).hom.op (fW (F.1.map i.hom.op s)) := by congr 1
  rw [rhs_eq, hfW (Vf p) (hVfB p) (hVfle p)]
  -- Now both sides are η.app(...)(F.1.map ... s), compose F maps
  simp only [← Functor.map_comp_apply]
  congr 1

/-- A map described on basis elements by `η` agrees with `η` on a basis element,
so the extension constructed for fullness restricts back to `η`. -/
private lemma full_lift (F G : TopCat.Sheaf (Type u) X)
    (η : (restrictPresheafFunctor B).obj F.1 ⟶ (restrictPresheafFunctor B).obj G.1)
    (V : Opens X) (hVB : V ∈ B) (s : F.1.obj (op V))
    (fV : F.1.obj (op V) → G.1.obj (op V))
    (hfV : ∀ (W : Opens X) (hWB : W ∈ B) (hWV : W ≤ V),
      G.1.map hWV.hom.op (fV s) = η.app (op ⟨W, hWB⟩) (F.1.map hWV.hom.op s)) :
    fV s = η.app (op ⟨V, hVB⟩) s := by
  have h := hfV V hVB (le_refl V)
  have hid : (le_refl V).hom = 𝟙 V := rfl
  rw [hid, op_id, F.1.map_id, G.1.map_id] at h
  exact h

/-- The restriction functor is full: a morphism between the restrictions of two
sheaves on `X` extends to a morphism of the sheaves themselves, by gluing the
images of the local restrictions of a section over a basis cover. -/
private lemma restrictFunctor_full (hB : Opens.IsBasis B) :
    (restrictFunctor B hB).Full := by
  constructor
  intro F G φ
  let η := φ.hom
  -- Step 1: For each U and s, construct the glued section and its key property
  have app_exists : ∀ (U : (Opens X)ᵒᵖ) (s : F.1.obj U),
      ∃ (t : G.1.obj U), ∀ (V : Opens X) (hVB : V ∈ B) (hVU : V ≤ U.unop),
        G.1.map hVU.hom.op t = η.app (op ⟨V, hVB⟩) (F.1.map hVU.hom.op s) := by
    intro U s
    obtain ⟨Vf, hVfB, hVfle, hVcov⟩ := exists_basis_cover B hB U.unop (fun _ => U.unop)
      (fun p => p.2) fun _ => le_rfl
    let sf : (p : ↑(U.unop : Opens X)) → G.1.obj (op (Vf p)) :=
      fun p => η.app (op ⟨Vf p, hVfB p⟩) (F.1.map (hVfle p).hom.op s)
    have hcompat : TopCat.Presheaf.IsCompatible G.1 Vf sf :=
      full_compat B hB F G η U.unop s Vf hVfB hVfle
    obtain ⟨t, ht, _⟩ := sheaf_unique_gluing G Vf sf hcompat
    refine ⟨G.1.map (eqToHom (congrArg op hVcov)) t, fun V hVB hVU => ?_⟩
    rw [← Functor.map_comp_apply]
    -- Both sides in G(V). Cover V by (Vf p ⊓ V), then each by basis elements.
    have hVsup : V ≤ ⨆ p, Vf p := hVU.trans_eq hVcov.symm
    have hcov_V : ⨆ p, Vf p ⊓ V = V := by
      apply le_antisymm
      · exact iSup_le (fun p => inf_le_right)
      · intro x hx; obtain ⟨p, hp⟩ := Opens.mem_iSup.mp (hVsup hx)
        exact Opens.mem_iSup.mpr ⟨p, ⟨hp, hx⟩⟩
    apply sheaf_eq_of_cover G (fun p => Vf p ⊓ V) V hcov_V
    intro p
    simp only [← Functor.map_comp_apply]
    obtain ⟨Zf, hZfB, hZfle, hZcov⟩ := exists_basis_cover B hB (Vf p ⊓ V) (fun _ => Vf p ⊓ V)
      (fun r => r.2) fun _ => le_rfl
    apply sheaf_eq_of_cover G Zf (Vf p ⊓ V) hZcov
    intro r
    have hZp : Zf r ≤ Vf p := (hZfle r).trans inf_le_left
    have hZV : Zf r ≤ V := (hZfle r).trans inf_le_right
    have hZU : Zf r ≤ U.unop := hZV.trans hVU
    simp only [← Functor.map_comp_apply]
    have lhs_eq : G.1.map (hZp.trans (le_iSup Vf p)).hom.op t =
        η.app (op ⟨Zf r, hZfB r⟩) (F.1.map hZU.hom.op s) := by
      have factored : G.1.map (hZp.trans (le_iSup Vf p)).hom.op t =
          G.1.map hZp.hom.op (G.1.map (Opens.leSupr Vf p).op t) := by
        rw [← Functor.map_comp_apply]; congr 1
      rw [factored, show G.1.map (Opens.leSupr Vf p).op t = sf p from ht p]
      rw [show (ConcreteCategory.hom (G.1.map hZp.hom.op))
            (η.app (op ⟨Vf p, hVfB p⟩) (F.1.map (hVfle p).hom.op s)) =
          η.app (op ⟨Zf r, hZfB r⟩) (F.1.map hZp.hom.op (F.1.map (hVfle p).hom.op s)) from
        (nat_on_basis B F G η (Vf p) (hVfB p) (Zf r) (hZfB r) hZp _).symm]
      rw [← Functor.map_comp_apply (self := F.1)]; congr 1
    have rhs_eq : G.1.map hZV.hom.op (η.app (op ⟨V, hVB⟩) (F.1.map hVU.hom.op s)) =
        η.app (op ⟨Zf r, hZfB r⟩) (F.1.map hZU.hom.op s) := by
      rw [show G.1.map hZV.hom.op (η.app (op ⟨V, hVB⟩) (F.1.map hVU.hom.op s)) =
          η.app (op ⟨Zf r, hZfB r⟩) (F.1.map hZV.hom.op (F.1.map hVU.hom.op s)) from
        (nat_on_basis B F G η V hVB (Zf r) (hZfB r) hZV _).symm]
      rw [← Functor.map_comp_apply (self := F.1)]; congr 1
    have goal_eq : G.1.map (hZp.trans (le_iSup Vf p)).hom.op t =
        G.1.map hZV.hom.op (η.app (op ⟨V, hVB⟩) (F.1.map hVU.hom.op s)) :=
      lhs_eq.trans rhs_eq.symm
    convert goal_eq using 1
    · exact map_congr_of_hom_eq G.1 _ _ t
    · exact map_congr_of_hom_eq G.1 _ _ _
  -- Step 2: Define the nat trans
  let app : ∀ (U : (Opens X)ᵒᵖ), F.1.obj U → G.1.obj U := fun U s => (app_exists U s).choose
  have app_prop : ∀ (U : (Opens X)ᵒᵖ) (s : F.1.obj U) (V : Opens X) (hVB : V ∈ B) (hVU : V ≤
      U.unop),
      G.1.map hVU.hom.op (app U s) = η.app (op ⟨V, hVB⟩) (F.1.map hVU.hom.op s) :=
    fun U s => (app_exists U s).choose_spec
  refine ⟨⟨{ app := fun U => ↾(app U), naturality := ?_ }⟩, ?_⟩
  · -- Naturality: for f : U ⟶ V, F.map f ≫ app V = app U ≫ G.map f
    -- i.e., app V (F.1.map f s) = G.1.map f (app U s) for all s
    intro U V f
    apply ConcreteCategory.hom_ext
    intro s
    -- Goal: (F.1.map f ≫ ↾(app V)) s = (↾(app U) ≫ G.1.map f) s
    have hi : V.unop ≤ U.unop := leOfHom f.unop
    have key := full_naturality B hB F G η U.unop V.unop hi s (app U) (app V)
      (fun W hWB hWU => app_prop U s W hWB hWU)
      (fun W hWB hWV => app_prop V (F.1.map f s) W hWB hWV)
    exact key.symm
  · -- Lifting: (restrictFunctor B hB).map ⟨f⟩ = φ
    apply InducedCategory.Hom.ext
    apply NatTrans.ext
    funext V
    apply ConcreteCategory.hom_ext
    intro s
    exact full_lift B F G η V.unop.obj V.unop.property s
      (app (op V.unop.obj))
      (fun W hWB hWV => app_prop (op V.unop.obj) s W hWB hWV)

/-- The restriction functor is essentially surjective: a sheaf `G` on `B` is the
restriction of the sheaf on `X` whose sections over an open `U` are the families
`(s_V)` of sections of `G`, indexed by the basis elements `V ≤ U`, that are
compatible under restriction. -/
private lemma restrictFunctor_essSurj (hB : Opens.IsBasis B) :
    (restrictFunctor B hB).EssSurj := by
  constructor
  intro G
  -- The extension presheaf: sections over `U` are compatible families of sections
  -- of `G` indexed by the basis elements contained in `U`.
  let Fext : (Opens X)ᵒᵖ ⥤ Type u :=
    { obj := fun U => { f : (V : BasisCat B) → (V.obj ≤ U.unop) → G.obj.obj (op V) //
        ∀ (V W : BasisCat B) (hV : V.obj ≤ U.unop) (hW : W.obj ≤ U.unop) (hWV : W.obj ≤ V.obj),
          G.obj.map (basisHom B hWV).op (f V hV) = f W hW }
      map := fun {U W} i => ↾(fun f =>
        ⟨fun V hV => f.1 V (hV.trans (leOfHom i.unop)),
         fun V V' hV hV' hle =>
           f.2 V V' (hV.trans (leOfHom i.unop)) (hV'.trans (leOfHom i.unop)) hle⟩)
      map_id := fun U => by ext ⟨f, hf⟩; rfl
      map_comp := fun f g => by ext ⟨s, hs⟩; rfl }
  -- Helper: compatibility at extPresheaf level gives pointwise equality
  have compat_pw : ∀ {ι : Type u} (U : ι → Opens X)
      (sf : (i : ι) → Fext.obj (op (U i)))
      (hcompat : TopCat.Presheaf.IsCompatible Fext U sf)
      (i j : ι) (W : BasisCat B) (hWi : W.obj ≤ U i) (hWj : W.obj ≤ U j),
      (sf i).1 W hWi = (sf j).1 W hWj := by
    intro ι U sf hcompat i j W hWi hWj
    have h : Fext.map (Opens.infLELeft (U i) (U j)).op (sf i) =
             Fext.map (Opens.infLERight (U i) (U j)).op (sf j) := hcompat i j
    exact congrArg (fun x => x.1 W (le_inf hWi hWj)) h
  -- Step 2: Show Fext is a sheaf
  have hFext_sheaf : TopCat.Presheaf.IsSheaf Fext := by
    rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types]
    intro ι U sf hcompat
    -- For each V ∈ B with V ≤ ⨆ U i, construct section via G's glue.
    -- Strengthened glue_V: also exports the restriction property.
    have glue_V : ∀ (V : BasisCat B) (hV : V.obj ≤ ⨆ i, U i),
        ∃ (t : G.obj.obj (op V)),
          (∀ (i : ι) (hVi : V.obj ≤ U i), (sf i).1 V hVi = t) ∧
          (∀ (W : BasisCat B) (hWV : W.obj ≤ V.obj) (j : ι) (hWj : W.obj ≤ U j),
            G.obj.map (basisHom B hWV).op t = (sf j).1 W hWj) := by
      intro V hV
      obtain ⟨ip, 𝒰, hWV, hWU, hcov⟩ := exists_basis_cover_subordinate B hB V.obj U hV
      let sec : (p : ↑(V.obj : Opens X)) → G.obj.obj (op (𝒰 p)) :=
        fun p => (sf (ip p)).1 (𝒰 p) (hWU p)
      have sec_compat : ∀ p q (W : BasisCat B) (hWp : W.obj ≤ (𝒰 p).obj) (hWq : W.obj ≤ (𝒰 q).obj),
          G.obj.restrictMap B hWp (sec p) = G.obj.restrictMap B hWq (sec q) := by
        intro p q W hWp hWq
        rw [PresheafOnBasis.restrictMap_apply, PresheafOnBasis.restrictMap_apply]
        have lhs : G.obj.map (basisHom B hWp).op (sec p) = (sf (ip p)).1 W (hWp.trans (hWU p)) :=
          (sf (ip p)).2 (𝒰 p) W (hWU p) (hWp.trans (hWU p)) hWp
        have rhs : G.obj.map (basisHom B hWq).op (sec q) = (sf (ip q)).1 W (hWq.trans (hWU q)) :=
          (sf (ip q)).2 (𝒰 q) W (hWU q) (hWq.trans (hWU q)) hWq
        rw [lhs, rhs]
        exact compat_pw U sf hcompat (ip p) (ip q) W (hWp.trans (hWU p)) (hWq.trans (hWU q))
      obtain ⟨t, ht⟩ := G.property.glue V 𝒰 hcov sec sec_compat
      refine ⟨t, ⟨?_, ?_⟩⟩
      · -- First property: ∀ i (hVi : V ≤ U i), (sf i).1 V hVi = t
        intro i hVi
        apply G.property.separated V 𝒰 hcov ((sf i).1 V hVi) t
        intro p
        rw [ht p]
        rw [PresheafOnBasis.restrictMap_apply]
        have step1 := (sf i).2 V (𝒰 p) hVi ((hWV p).trans hVi) (hWV p)
        have step2 : (sf i).1 (𝒰 p) ((hWV p).trans hVi) = sec p :=
          compat_pw U sf hcompat i (ip p) (𝒰 p) ((hWV p).trans hVi) (hWU p)
        convert step1.trans step2 using 1
      · -- Second property: restriction to sub-basis elements
        -- For W ≤ V with W ≤ U j, show G.obj.map(W ≤ V)(t) = (sf j).1 W hWj
        intro W hW_le_V j hWj
        -- Use G.property.separated on W with basis cover of W intersected with cover of V
        -- Cover W by basis elements inside W ∩ 𝒰 q for various q
        obtain ⟨kp, 𝒰Y, hYW, hY𝒰, hcovY⟩ := exists_basis_cover_subordinate B hB W.obj
          (fun q => (𝒰 q).obj) (hW_le_V.trans_eq hcov.symm)
        apply G.property.separated W 𝒰Y hcovY
        intro r
        simp only [PresheafOnBasis.restrictMap, ← Functor.map_comp_apply]
        -- LHS: G.obj.map(𝒰Y r ≤ V)(t). Since 𝒰Y r ≤ 𝒰(kp r), use ht (the internal gluing):
        --   G.obj.map(𝒰Y r ≤ V)(t) = G.obj.map(𝒰Y r ≤ 𝒰(kp r))(G.obj.map(𝒰(kp r) ≤ V)(t))
        --   = G.obj.map(𝒰Y r ≤ 𝒰(kp r))(sec (kp r))   [by ht (kp r)]
        --   = (sf (ip (kp r))).1 (𝒰Y r) _   [by (sf (ip (kp r))).2]
        have lhs_step1 : G.obj.map (basisHom B ((hYW r).trans hW_le_V)).op t =
            G.obj.map (basisHom B (hY𝒰 r)).op (G.obj.map (basisHom B (hWV (kp r))).op t) := by
          rw [← Functor.map_comp_apply]; congr 1
        have lhs_step2 : G.obj.map (basisHom B (hWV (kp r))).op t = sec (kp r) := ht (kp r)
        have lhs_step3 : G.obj.map (basisHom B (hY𝒰 r)).op (sec (kp r)) =
            (sf (ip (kp r))).1 (𝒰Y r) ((hY𝒰 r).trans (hWU (kp r))) :=
          (sf (ip (kp r))).2 (𝒰 (kp r)) (𝒰Y r) (hWU (kp r)) ((hY𝒰 r).trans (hWU (kp r))) (hY𝒰 r)
        -- RHS: G.obj.map(𝒰Y r ≤ W)((sf j).1 W hWj) = (sf j).1 (𝒰Y r) ((hYW r).trans hWj)
        --   [by (sf j).2]
        have rhs_step : G.obj.map (basisHom B (hYW r)).op ((sf j).1 W hWj) =
            (sf j).1 (𝒰Y r) ((hYW r).trans hWj) :=
          (sf j).2 W (𝒰Y r) hWj ((hYW r).trans hWj) (hYW r)
        -- Both equal by compat_pw
        have both_eq : (sf (ip (kp r))).1 (𝒰Y r) ((hY𝒰 r).trans (hWU (kp r))) =
            (sf j).1 (𝒰Y r) ((hYW r).trans hWj) :=
          compat_pw U sf hcompat (ip (kp r)) j (𝒰Y r) ((hY𝒰 r).trans (hWU (kp r))) ((hYW r).trans
              hWj)
        -- Assemble
        have lhs_final : G.obj.map (basisHom B ((hYW r).trans hW_le_V)).op t =
            (sf (ip (kp r))).1 (𝒰Y r) ((hY𝒰 r).trans (hWU (kp r))) := by
          rw [lhs_step1, lhs_step2, lhs_step3]
        exact (basisMap_congr_of_hom_eq B G.obj _
            (basisHom B ((hYW r).trans hW_le_V)).op t).trans
          (lhs_final.trans (both_eq.trans rhs_step.symm))
    -- Now construct the glued section
    -- Define t : Fext.obj (op (⨆ i, U i))
    let tval : (V : BasisCat B) → (V.obj ≤ ⨆ i, U i) → G.obj.obj (op V) :=
      fun V hV => (glue_V V hV).choose
    have tval_prop : ∀ (V : BasisCat B) (hV : V.obj ≤ ⨆ i, U i),
        ∀ (i : ι) (hVi : V.obj ≤ U i), (sf i).1 V hVi = tval V hV :=
      fun V hV => (glue_V V hV).choose_spec.1
    have tval_restrict : ∀ (V : BasisCat B) (hV : V.obj ≤ ⨆ i, U i)
        (W : BasisCat B) (hWV : W.obj ≤ V.obj) (j : ι) (hWj : W.obj ≤ U j),
        G.obj.map (basisHom B hWV).op (tval V hV) = (sf j).1 W hWj :=
      fun V hV => (glue_V V hV).choose_spec.2
    have tval_compat : ∀ (V W : BasisCat B) (hV : V.obj ≤ ⨆ i, U i) (hW : W.obj ≤ ⨆ i, U i)
        (hWV : W.obj ≤ V.obj), G.obj.map (basisHom B hWV).op (tval V hV) = tval W hW := by
      intro V W hV hW hWV
      -- Cover W by basis elements inside U j for some j. Use tval_restrict and tval_prop.
      obtain ⟨jp, 𝒰W, hZW, hZU, hcovW⟩ := exists_basis_cover_subordinate B hB W.obj U hW
      apply G.property.separated W 𝒰W hcovW
      intro p
      simp only [PresheafOnBasis.restrictMap, ← Functor.map_comp_apply]
      -- LHS: G.obj.map(𝒰W p ≤ V)(tval V hV) = (sf (jp p)).1 (𝒰W p) (hZU p)
      --   by tval_restrict V hV (𝒰W p) ((hZW p).trans hWV) (jp p) (hZU p)
      have lhs_eq : G.obj.map (basisHom B ((hZW p).trans hWV)).op (tval V hV) =
          (sf (jp p)).1 (𝒰W p) (hZU p) :=
        tval_restrict V hV (𝒰W p) ((hZW p).trans hWV) (jp p) (hZU p)
      -- RHS: G.obj.map(𝒰W p ≤ W)(tval W hW) = (sf (jp p)).1 (𝒰W p) (hZU p)
      --   by tval_restrict W hW (𝒰W p) (hZW p) (jp p) (hZU p)
      have rhs_eq : G.obj.map (basisHom B (hZW p)).op (tval W hW) =
          (sf (jp p)).1 (𝒰W p) (hZU p) :=
        tval_restrict W hW (𝒰W p) (hZW p) (jp p) (hZU p)
      exact (basisMap_congr_of_hom_eq B G.obj _
          (basisHom B ((hZW p).trans hWV)).op (tval V hV)).trans
        (lhs_eq.trans rhs_eq.symm)
    -- Construct t as a compatible family
    let t : Fext.obj (op (⨆ i, U i)) := ⟨tval, tval_compat⟩
    -- Show IsGluing
    have t_gluing : TopCat.Presheaf.IsGluing Fext U sf t := by
      intro i
      apply Subtype.ext
      funext V hV
      exact (tval_prop V (hV.trans (le_iSup U i)) i hV).symm
    -- Show uniqueness
    have t_unique : ∀ (t' : Fext.obj (op (⨆ i, U i))),
        TopCat.Presheaf.IsGluing Fext U sf t' → t' = t := by
      intro t' ht'
      apply Subtype.ext
      funext V hV
      -- Use separated on V with basis cover to show t'.1 V hV = tval V hV
      obtain ⟨jp, 𝒰V, hZV, hZU, hcovV⟩ := exists_basis_cover_subordinate B hB V.obj U hV
      apply G.property.separated V 𝒰V hcovV (t'.1 V hV) (tval V hV)
      intro p
      simp only [PresheafOnBasis.restrictMap]
      -- LHS: by t'.2, then ht'
      have lhs_step1 : G.obj.map (basisHom B (hZV p)).op (t'.1 V hV) =
          t'.1 (𝒰V p) ((hZV p).trans hV) :=
        t'.2 V (𝒰V p) hV ((hZV p).trans hV) (hZV p)
      -- t'.1 (𝒰V p) ((hZV p).trans hV) = t'.1 (𝒰V p) ((hZU p).trans (le_iSup U (jp p)))
      -- by proof irrelevance (same element, different proof of same inequality)
      have lhs_step2 : t'.1 (𝒰V p) ((hZV p).trans hV) = (sf (jp p)).1 (𝒰V p) (hZU p) :=
        congrArg (fun x => x.1 (𝒰V p) (hZU p)) (ht' (jp p))
      -- RHS: by tval_restrict
      have rhs_eq : G.obj.map (basisHom B (hZV p)).op (tval V hV) =
          (sf (jp p)).1 (𝒰V p) (hZU p) :=
        tval_restrict V hV (𝒰V p) (hZV p) (jp p) (hZU p)
      convert (lhs_step1.trans lhs_step2).trans rhs_eq.symm using 1
    exact ⟨t, t_gluing, t_unique⟩
  let Fsheaf : TopCat.Sheaf (Type u) X := ⟨Fext, hFext_sheaf⟩
  -- The isomorphism `Fext|_B ≅ G` sends a compatible family over a basis element `V`
  -- to its component at `V`; the inverse sends `s` to the family of restrictions of `s`.
  refine ⟨Fsheaf, ⟨InducedCategory.isoMk (NatIso.ofComponents (fun V => ?_) (fun {V W} f => ?_))⟩⟩
  · -- Component iso at V : (BasisCat B)ᵒᵖ
    -- Need: ((restrictPresheafFunctor B).obj Fext).obj V ≅ G.obj.obj V
    -- LHS = Fext.obj (op V.unop.obj) = { compatible families on V.unop.obj }
    -- RHS = G.obj.obj V
    refine { hom := ↾(fun cf => cf.1 V.unop (le_refl _))
             inv := ↾(fun s => ⟨fun W hW => G.obj.map (basisHom B hW).op s,
               fun W1 W2 hW1 hW2 hle => ?_⟩)
             hom_inv_id := ?_
             inv_hom_id := ?_ }
    · -- Compatibility of restriction maps under composition.
      rw [← Functor.map_comp_apply]; congr 1
    · -- hom_inv_id: inv (hom cf) = cf
      apply ConcreteCategory.hom_ext
      intro ⟨cf, hcf⟩
      apply Subtype.ext
      funext W hW
      exact hcf V.unop W (le_refl _) hW hW
    · -- inv_hom_id: hom (inv s) = s, i.e., G.obj.map (basisHom B (le_refl _)).op s = s
      apply ConcreteCategory.hom_ext
      intro s
      simp only [ConcreteCategory.comp_apply, TypeCat.ofHom_apply, ConcreteCategory.id_apply]
      have : (basisHom B (le_refl V.unop.obj)) = 𝟙 V.unop := by
        ext; rfl
      rw [this, op_id, G.obj.map_id]
      rfl
  · -- Naturality
    apply ConcreteCategory.hom_ext
    intro ⟨cf, hcf⟩
    -- Goal: cf W.unop (something) = G.obj.map f (cf V.unop (le_refl _))
    -- The 'something' is (le_refl W.unop.obj).trans (leOfHom ((basisInclusion B).map f.unop))
    -- = leOfHom ((basisInclusion B).map f.unop) = W.unop.obj ≤ V.unop.obj
    -- G.obj.map f = G.obj.map (basisHom B h).op where h : W.unop.obj ≤ V.unop.obj
    -- Use hcf directly
    have h : W.unop.obj ≤ V.unop.obj := leOfHom f.unop.hom
    have key := hcf V.unop W.unop (le_refl _) h h
    exact key.symm

/-- **Stacks 009O.** Let `X` be a topological space and let `B` be a basis for
the topology on `X`. The restriction-to-basis functor `r : Sh(X) ⥤ Sh(B)` is an
equivalence of categories. -/
@[stacks 009O]
theorem restrictFunctor_isEquivalence (hB : Opens.IsBasis B) :
    (restrictFunctor (X := X) B hB).IsEquivalence := by
  have hfaith := restrictFunctor_faithful B hB
  have hfull := restrictFunctor_full B hB
  have hesssurj := restrictFunctor_essSurj B hB
  exact ⟨hfaith, hfull, hesssurj⟩

end Stacks.OpensBasis
