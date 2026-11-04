module

public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalIdealRestriction
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Restriction data glued from a local rule

Let `φ : 𝒜 ⟶ ℬ` be a morphism of sheaves of commutative rings on a topological space `X` and let
`𝒢` be a sheaf of `ℬ`-modules. A restriction datum `Ker φ ⟶ 𝒢`
(`Stacks.Sites.Conormal.IdealRestriction`) is often only describable locally: a local section
of the kernel is, near each point, of a shape on which its value is prescribed. This file glues
such a prescription.

A *local rule* is a relation `R V a g` between kernel sections `a` and sections `g` of `𝒢` over
the same open, which

* is locally satisfiable: every kernel section has, near every point, a value;
* has at most one value on each open;
* is stable under restriction;
* is additive, and `𝒜`-linear through `φ` locally.

Its glued restriction datum takes `a` to the unique section of `𝒢` which locally is the value
of `a`.

## Main definitions

* `Stacks.Sites.Conormal.IdealRestriction.LocalRule`: a local rule.
* `Stacks.Sites.Conormal.IdealRestriction.LocalRule.toIdealRestriction`: its glued restriction
  datum.

## Main results

* `Stacks.Sites.Conormal.IdealRestriction.LocalRule.toIdealRestriction_app_eq`: the glued datum
  takes a kernel section to any of its values.
* `Stacks.Sites.Conormal.IdealRestriction.LocalRule.toIdealRestriction_app_eq_of_locally`: and
  to any section which is locally a value of it.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.Sites.Conormal.IdealRestriction

variable {X : TopCat.{u}} {A B : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  (φ : A ⟶ B)
  (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf B))

/-- The restriction of a section of the kernel ideal of `φ` to a smaller open. -/
def kernelRes {U V : Opens X} (h : V ≤ U) (a : ↥(kernelIdeal φ.hom (op U))) :
    ↥(kernelIdeal φ.hom (op V)) :=
  ⟨(A.obj.map (homOfLE h).op).hom a.1, map_kernel φ.hom (homOfLE h).op a.2⟩

variable {φ} in
/-- The underlying section of a restricted kernel section is the restriction in `𝒜`. -/
@[simp] theorem kernelRes_val {U V : Opens X} (h : V ≤ U) (a : ↥(kernelIdeal φ.hom (op U))) :
    (kernelRes φ h a).1 = (A.obj.map (homOfLE h).op).hom a.1 :=
  rfl

variable {φ} in
/-- Restricting a kernel section twice is restricting it once. -/
theorem kernelRes_kernelRes {U V W : Opens X} (h : V ≤ U) (h' : W ≤ V)
    (a : ↥(kernelIdeal φ.hom (op U))) :
    kernelRes φ h' (kernelRes φ h a) = kernelRes φ (h'.trans h) a := by
  refine Subtype.ext ?_
  show (A.obj.map (homOfLE h').op).hom ((A.obj.map (homOfLE h).op).hom a.1) =
    (A.obj.map (homOfLE (h'.trans h)).op).hom a.1
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

variable {φ} in
/-- Restriction of kernel sections is additive. -/
theorem kernelRes_add {U V : Opens X} (h : V ≤ U) (a b : ↥(kernelIdeal φ.hom (op U))) :
    kernelRes φ h (a + b) = kernelRes φ h a + kernelRes φ h b :=
  Subtype.ext (map_add (A.obj.map (homOfLE h).op).hom a.1 b.1)

variable {φ} in
/-- Restricting `r • a` gives the restriction of `r` acting on the restriction of `a`. -/
theorem kernelRes_smul {U V : Opens X} (h : V ≤ U) (r : ↥(A.obj.obj (op U)))
    (a : ↥(kernelIdeal φ.hom (op U))) :
    kernelRes φ h (r • a) = (A.obj.map (homOfLE h).op).hom r • kernelRes φ h a :=
  Subtype.ext (map_mul (A.obj.map (homOfLE h).op).hom r a.1)

variable {G} in
/-- Restricting a section of `𝒢` twice is restricting it once. -/
theorem sectionRes_sectionRes {U V W : Opens X} (h : V ≤ U) (h' : W ≤ V)
    (g : ↥(G.val.obj (op U))) :
    G.val.map (homOfLE h').op (G.val.map (homOfLE h).op g) =
      G.val.map (homOfLE (h'.trans h)).op g := by
  rw [← PresheafOfModules.map_comp_apply]
  rfl

variable {G} in
/-- Restriction of sections of `𝒢` is additive. -/
theorem sectionRes_add {U V : Opens X} (h : V ≤ U) (g g' : ↥(G.val.obj (op U))) :
    (G.val.map (homOfLE h).op (g + g') : ↥(G.val.obj (op V))) =
      (G.val.map (homOfLE h).op g : ↥(G.val.obj (op V))) +
        (G.val.map (homOfLE h).op g' : ↥(G.val.obj (op V))) :=
  map_add _ _ _

variable {G} in
/-- Restricting `r • g` gives the restriction of `r` acting on the restriction of `g`. -/
theorem sectionRes_smul {U V : Opens X} (h : V ≤ U)
    (r : ↥((Stacks.SheafOfModules.Tensor.ringSheaf B).obj.obj (op U)))
    (g : ↥(G.val.obj (op U))) :
    (G.val.map (homOfLE h).op (r • g) : ↥(G.val.obj (op V))) =
      ((Stacks.SheafOfModules.Tensor.ringSheaf B).obj.map (homOfLE h).op).hom r •
        (G.val.map (homOfLE h).op g : ↥(G.val.obj (op V))) :=
  PresheafOfModules.map_smul _ _ _ _

variable {φ} in
/-- The scalar `presentationScalar φ` commutes with restriction: restricting the image of `r` from
`U` to `W` equals restricting from `V` to `W` the image of the restriction of `r` to `V`. -/
theorem presentationScalar_res {U V W : Opens X} (hV : V ≤ U) (hW : W ≤ V)
    (r : ↥(A.obj.obj (op U))) :
    ((Stacks.SheafOfModules.Tensor.ringSheaf B).obj.map (homOfLE (hW.trans hV)).op).hom
        (presentationScalar φ (op U) r) =
      ((Stacks.SheafOfModules.Tensor.ringSheaf B).obj.map (homOfLE hW).op).hom
        (presentationScalar φ (op V) ((A.obj.map (homOfLE hV).op).hom r)) := by
  show (B.obj.map (homOfLE (hW.trans hV)).op).hom ((φ.hom.app (op U)).hom r) =
    (B.obj.map (homOfLE hW).op).hom ((φ.hom.app (op V)).hom ((A.obj.map (homOfLE hV).op).hom r))
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
    ← φ.hom.naturality, ← φ.hom.naturality, ← Category.assoc, ← Functor.map_comp]
  rfl

/-- A local rule prescribing the values of a restriction datum `Ker φ ⟶ 𝒢`. -/
structure LocalRule where
  /-- `R V a g`: the section `g` of `𝒢` is a value of the kernel section `a` over `V`. -/
  R : ∀ V : Opens X, ↥(kernelIdeal φ.hom (op V)) → ↥(G.val.obj (op V)) → Prop
  /-- Every kernel section has a value near every point. -/
  exists_local : ∀ {U : Opens X} (a : ↥(kernelIdeal φ.hom (op U))) (x : X), x ∈ U →
    ∃ (V : Opens X) (h : V ≤ U), x ∈ V ∧ ∃ g, R V (kernelRes φ h a) g
  /-- A kernel section has at most one value on each open. -/
  unique : ∀ {V : Opens X} {a : ↥(kernelIdeal φ.hom (op V))} {g g' : ↥(G.val.obj (op V))},
    R V a g → R V a g' → g = g'
  /-- Values restrict to values. -/
  res : ∀ {V W : Opens X} (h : W ≤ V) {a : ↥(kernelIdeal φ.hom (op V))}
    {g : ↥(G.val.obj (op V))}, R V a g → R W (kernelRes φ h a) (G.val.map (homOfLE h).op g)
  /-- Values are additive. -/
  add : ∀ {V : Opens X} {a b : ↥(kernelIdeal φ.hom (op V))} {g g' : ↥(G.val.obj (op V))},
    R V a g → R V b g' → R V (a + b) (g + g')
  /-- Values are linear over `𝒜` acting through `φ`, locally. -/
  smul : ∀ {V : Opens X} {a : ↥(kernelIdeal φ.hom (op V))} {g : ↥(G.val.obj (op V))},
    R V a g → ∀ (r : ↥(A.obj.obj (op V))) (x : X), x ∈ V →
      ∃ (W : Opens X) (h : W ≤ V), x ∈ W ∧
        R W (kernelRes φ h (r • a)) (G.val.map (homOfLE h).op (presentationScalar φ (op V) r • g))

namespace LocalRule

variable {φ G} (L : LocalRule φ G)

/-- `𝒢` as a sheaf of abelian groups on `X`. -/
abbrev abSheaf : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨G.val.presheaf, G.isSheaf⟩

/-- The open around a point of `U` on which a kernel section has a chosen value. -/
def localOpen {U : Opens X} (a : ↥(kernelIdeal φ.hom (op U))) (x : U) : Opens X :=
  Classical.choose (L.exists_local a x.1 x.2)

/-- The open `localOpen a x` is contained in `U`. -/
theorem localOpen_le {U : Opens X} (a : ↥(kernelIdeal φ.hom (op U))) (x : U) :
    L.localOpen a x ≤ U :=
  Classical.choose (Classical.choose_spec (L.exists_local a x.1 x.2))

/-- The point `x` lies in `localOpen a x`. -/
theorem mem_localOpen {U : Opens X} (a : ↥(kernelIdeal φ.hom (op U))) (x : U) :
    x.1 ∈ L.localOpen a x :=
  (Classical.choose_spec (Classical.choose_spec (L.exists_local a x.1 x.2))).1

/-- The chosen value of a kernel section near a point. -/
def localValue {U : Opens X} (a : ↥(kernelIdeal φ.hom (op U))) (x : U) :
    ↥(G.val.obj (op (L.localOpen a x))) :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (L.exists_local a x.1 x.2))).2

/-- The chosen value `localValue a x` is a value of the restriction of `a` to `localOpen a x`. -/
theorem localValue_spec {U : Opens X} (a : ↥(kernelIdeal φ.hom (op U))) (x : U) :
    L.R _ (kernelRes φ (L.localOpen_le a x) a) (L.localValue a x) :=
  Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec (L.exists_local a x.1 x.2))).2

/-- A value of a restricted kernel section restricts to a value of the doubly restricted one. -/
private theorem R_res_res {U V W : Opens X} {a : ↥(kernelIdeal φ.hom (op U))}
    (hV : V ≤ U) (hW : W ≤ V) {g : ↥(G.val.obj (op V))} (hg : L.R V (kernelRes φ hV a) g) :
    L.R W (kernelRes φ (hW.trans hV) a) (G.val.map (homOfLE hW).op g) := by
  rw [← kernelRes_kernelRes hV hW]
  exact L.res hW hg

/-- Two values of restrictions of one kernel section agree where both are defined. -/
theorem res_eq_of_R {U V V' W : Opens X} (a : ↥(kernelIdeal φ.hom (op U))) (hV : V ≤ U)
    (hV' : V' ≤ U) (hW : W ≤ V) (hW' : W ≤ V') {g : ↥(G.val.obj (op V))}
    {g' : ↥(G.val.obj (op V'))} (hg : L.R V (kernelRes φ hV a) g)
    (hg' : L.R V' (kernelRes φ hV' a) g') :
    G.val.map (homOfLE hW).op g = G.val.map (homOfLE hW').op g' := by
  exact L.unique (L.R_res_res hV hW hg) (L.R_res_res hV' hW' hg')

/-- There is a unique section of `𝒢` over `U` restricting to the chosen value of a kernel section
on each `localOpen a x`. -/
theorem exists_glue {U : Opens X} (a : ↥(kernelIdeal φ.hom (op U))) :
    ∃! s : ↥(G.val.obj (op U)), ∀ x : U,
      G.val.map (homOfLE (L.localOpen_le a x)).op s = L.localValue a x := by
  have hc : TopCat.Presheaf.IsCompatible (abSheaf (G := G)).1 (fun x : U => L.localOpen a x)
      (fun x => L.localValue a x) := fun x y =>
    L.res_eq_of_R a _ _ inf_le_left inf_le_right (L.localValue_spec a x) (L.localValue_spec a y)
  exact TopCat.Sheaf.existsUnique_gluing' (abSheaf (G := G)) (fun x : U => L.localOpen a x) U
    (fun x => homOfLE (L.localOpen_le a x))
    (fun x hx => Opens.mem_iSup.2 ⟨⟨x, hx⟩, L.mem_localOpen a ⟨x, hx⟩⟩)
    (fun x => L.localValue a x) hc

/-- The glued value of a kernel section. -/
def glue {U : Opens X} (a : ↥(kernelIdeal φ.hom (op U))) : ↥(G.val.obj (op U)) :=
  Classical.choose (L.exists_glue a)

/-- The glued value restricts to the chosen value on each `localOpen a x`. -/
theorem glue_res_localOpen {U : Opens X} (a : ↥(kernelIdeal φ.hom (op U))) (x : U) :
    G.val.map (homOfLE (L.localOpen_le a x)).op (L.glue a) = L.localValue a x :=
  (Classical.choose_spec (L.exists_glue a)).1 x

/-- The glued value is locally a value. -/
theorem exists_R_glue {U : Opens X} (a : ↥(kernelIdeal φ.hom (op U))) (x : X) (hx : x ∈ U) :
    ∃ (V : Opens X) (h : V ≤ U), x ∈ V ∧
      L.R V (kernelRes φ h a) (G.val.map (homOfLE h).op (L.glue a)) :=
  ⟨_, L.localOpen_le a ⟨x, hx⟩, L.mem_localOpen a ⟨x, hx⟩, by
    rw [L.glue_res_localOpen]; exact L.localValue_spec a ⟨x, hx⟩⟩

/-- **A section which is locally a value of a kernel section is its glued value.** -/
theorem glue_eq_of_locally {U : Opens X} (a : ↥(kernelIdeal φ.hom (op U)))
    (s : ↥(G.val.obj (op U)))
    (hs : ∀ x ∈ U, ∃ (V : Opens X) (h : V ≤ U), x ∈ V ∧
      L.R V (kernelRes φ h a) (G.val.map (homOfLE h).op s)) :
    L.glue a = s := by
  choose V hV hxV hR using hs
  choose V' hV' hxV' hR' using L.exists_R_glue a
  refine TopCat.Sheaf.eq_of_locally_eq' (abSheaf (G := G))
    (fun x : U => V x.1 x.2 ⊓ V' x.1 x.2) U
    (fun x => homOfLE (inf_le_left.trans (hV x.1 x.2)))
    (fun x hx => Opens.mem_iSup.2 ⟨⟨x, hx⟩, ⟨hxV x hx, hxV' x hx⟩⟩) _ _ (fun x => ?_)
  have e := L.res_eq_of_R a (hV' x.1 x.2) (hV x.1 x.2) inf_le_right inf_le_left
    (hR' x.1 x.2) (hR x.1 x.2)
  show G.val.map _ (L.glue a) = G.val.map _ s
  rwa [sectionRes_sectionRes, sectionRes_sectionRes] at e

/-- A value of a kernel section is its glued value. -/
theorem glue_eq {U : Opens X} {a : ↥(kernelIdeal φ.hom (op U))} {g : ↥(G.val.obj (op U))}
    (h : L.R U a g) : L.glue a = g :=
  L.glue_eq_of_locally a g fun x hx => ⟨U, le_rfl, hx, by
    have := L.res (le_refl U) h
    convert this using 1⟩

/-- The glued value is a value on every small enough open around each point. -/
theorem exists_R_glue_forall {U : Opens X} (a : ↥(kernelIdeal φ.hom (op U))) (x : X)
    (hx : x ∈ U) :
    ∃ (V : Opens X) (_ : V ≤ U), x ∈ V ∧ ∀ (W : Opens X) (h : W ≤ U), W ≤ V →
      L.R W (kernelRes φ h a) (G.val.map (homOfLE h).op (L.glue a)) := by
  obtain ⟨V, hV, hxV, hR⟩ := L.exists_R_glue a x hx
  refine ⟨V, hV, hxV, fun W h hWV => ?_⟩
  rw [← sectionRes_sectionRes hV hWV]
  exact L.R_res_res hV hWV hR

/-- The glued value is additive. -/
theorem glue_add {U : Opens X} (a b : ↥(kernelIdeal φ.hom (op U))) :
    L.glue (a + b) = L.glue a + L.glue b := by
  refine L.glue_eq_of_locally _ _ fun x hx => ?_
  obtain ⟨V₁, hV₁, hx₁, h₁⟩ := L.exists_R_glue_forall a x hx
  obtain ⟨V₂, hV₂, hx₂, h₂⟩ := L.exists_R_glue_forall b x hx
  have hW : V₁ ⊓ V₂ ≤ U := inf_le_left.trans hV₁
  refine ⟨V₁ ⊓ V₂, hW, ⟨hx₁, hx₂⟩, ?_⟩
  have := L.add (h₁ _ hW inf_le_left) (h₂ _ hW inf_le_right)
  rw [← kernelRes_add] at this
  exact (congrArg (L.R _ _)
    (sectionRes_add (G := G) hW (L.glue a) (L.glue b))).mpr this

/-- The glued value is linear over `𝒜` acting through `φ`. -/
theorem glue_smul {U : Opens X} (r : ↥(A.obj.obj (op U))) (a : ↥(kernelIdeal φ.hom (op U))) :
    L.glue (r • a) = presentationScalar φ (op U) r • L.glue a := by
  refine L.glue_eq_of_locally _ _ fun x hx => ?_
  obtain ⟨V, hV, hxV, hR⟩ := L.exists_R_glue a x hx
  obtain ⟨W, hW, hxW, hR'⟩ := L.smul hR ((A.obj.map (homOfLE hV).op).hom r) x hxV
  refine ⟨W, hW.trans hV, hxW, ?_⟩
  rw [← kernelRes_smul, kernelRes_kernelRes] at hR'
  refine (congrArg (L.R _ _) ?_).mpr hR'
  refine (sectionRes_smul (G := G) (hW.trans hV) (presentationScalar φ (op U) r)
    (L.glue a)).trans ?_
  refine Eq.trans ?_ (sectionRes_smul (G := G) hW _ (G.val.map (homOfLE hV).op (L.glue a))).symm
  rw [presentationScalar_res hV hW, sectionRes_sectionRes]
  rfl

/-- The glued value of a restricted kernel section is the restriction of the glued value. -/
theorem glue_res {U V : Opens X} (h : V ≤ U) (a : ↥(kernelIdeal φ.hom (op U))) :
    L.glue (kernelRes φ h a) = G.val.map (homOfLE h).op (L.glue a) := by
  refine L.glue_eq_of_locally _ _ fun x hx => ?_
  obtain ⟨V', hV', hxV', hR⟩ := L.exists_R_glue_forall a x (h hx)
  refine ⟨V ⊓ V', inf_le_left, ⟨hx, hxV'⟩, ?_⟩
  rw [kernelRes_kernelRes, sectionRes_sectionRes]
  exact hR _ (inf_le_left.trans h) inf_le_right

/-- **The restriction datum glued from a local rule.** -/
def toIdealRestriction : IdealRestriction.{u, u, u, u} φ G where
  app U :=
    { toFun := fun a => L.glue (U := U.unop) a
      map_zero' := by
        have h := L.glue_add (U := U.unop) 0 0
        rw [add_zero] at h
        exact (add_eq_left.1 h.symm)
      map_add' := fun a b => L.glue_add a b }
  app_smul U r a := L.glue_smul r a
  app_map {U V} f a := L.glue_res (leOfHom f.unop) a

/-- The glued restriction datum takes a kernel section to its glued value. -/
theorem toIdealRestriction_app {U : Opens X} (a : ↥(kernelIdeal φ.hom (op U))) :
    L.toIdealRestriction.app (op U) a = L.glue a :=
  rfl

/-- The glued restriction datum takes a kernel section to its value. -/
theorem toIdealRestriction_app_eq {U : Opens X} {a : ↥(kernelIdeal φ.hom (op U))}
    {g : ↥(G.val.obj (op U))} (h : L.R U a g) : L.toIdealRestriction.app (op U) a = g :=
  L.glue_eq h

/-- The glued restriction datum takes a kernel section to any section which is locally a value
of it. -/
theorem toIdealRestriction_app_eq_of_locally {U : Opens X} (a : ↥(kernelIdeal φ.hom (op U)))
    (s : ↥(G.val.obj (op U)))
    (hs : ∀ x ∈ U, ∃ (V : Opens X) (h : V ≤ U), x ∈ V ∧
      L.R V (kernelRes φ h a) (G.val.map (homOfLE h).op s)) :
    L.toIdealRestriction.app (op U) a = s :=
  L.glue_eq_of_locally a s hs

end LocalRule

end Stacks.Sites.Conormal.IdealRestriction

end
