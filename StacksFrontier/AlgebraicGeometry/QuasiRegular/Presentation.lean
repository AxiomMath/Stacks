module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Geometry.RingedSpace.Basic
public import Mathlib.Geometry.RingedSpace.Stalks
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Sheaves of commutative rings presented by polynomials over the structure sheaf

Let `X` be a ringed space and let `r : ℕ`. A `StalkPresentation X r` is a family of commutative
rings `A x`, one for each point `x : X`, together with ring homomorphisms

`pres U x hx : (O_X(U))[T_1, ..., T_r] ⟶ A x`

for every open `U` and every `x ∈ U`, compatible with restriction, such that

* every element of `A x` is `pres V x _ p` for some neighbourhood `V` of `x` and some polynomial
  `p` with coefficients in `O_X(V)` (local surjectivity), and
* whenever `pres U x hx p = 0`, the same already holds at every point of some neighbourhood of
  `x` inside `U` (the vanishing locus of a polynomial relation is open).

Such data determine a sheaf of commutative rings: the sections over `U` are the families
`(s x)_{x ∈ U}` with `s x ∈ A x` which are locally of the form `pres V y _ p`. The two conditions
above say exactly that the stalk of this sheaf at `x` is `A x`, via evaluation at `x`. This is the
Godement construction of the sheafification of the presheaf `U ↦ (O_X(U))[T]/(relations)`.

## Main definitions

* `StalkPresentation`: the data above.
* `StalkPresentation.presheaf`, `StalkPresentation.sheaf`: the resulting sheaf of commutative
  rings.
* `StalkPresentation.ofSections`: the ring homomorphism `(O_X(U))[T] ⟶ Γ(U, F)` induced by `pres`.
* `StalkPresentation.stalkIso`: the identification of the stalk at `x` with `A x`.
* `StalkPresentation.Hom` and `StalkPresentation.Hom.sheafHom`: a morphism of presentations and
  the induced morphism of sheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.QuasiRegular

/-- The data presenting a sheaf of commutative rings on a ringed space `X` by polynomials in `r`
variables over the structure sheaf: a commutative ring `A x` at every point, local presentation
maps, and the two conditions (openness of vanishing, local surjectivity) that make evaluation at
`x` identify the stalk at `x` with `A x`. -/
structure StalkPresentation (X : RingedSpace.{u}) (r : ℕ) where
  /-- The ring attached to a point; it will be the stalk of the resulting sheaf. -/
  obj : X → CommRingCat.{u}
  /-- The local presentation: a polynomial with coefficients in `O_X(U)` determines an element of
  `A x` for each `x ∈ U`. -/
  pres (U : Opens X) (x : X) (hx : x ∈ U) :
    MvPolynomial (Fin r) (X.presheaf.obj (op U)) →+* obj x
  /-- The presentation maps are compatible with restriction of the coefficients. -/
  pres_res {U V : Opens X} (hUV : U ≤ V) (x : X) (hx : x ∈ U)
      (p : MvPolynomial (Fin r) (X.presheaf.obj (op V))) :
    pres V x (hUV hx) p
      = pres U x hx (MvPolynomial.map (X.presheaf.map (homOfLE hUV).op).hom p)
  /-- A polynomial relation which holds at `x` holds on a whole neighbourhood of `x`. -/
  pres_eq_zero_nhds (U : Opens X) (x : X) (hx : x ∈ U)
      (p : MvPolynomial (Fin r) (X.presheaf.obj (op U))) (h : pres U x hx p = 0) :
    ∃ (V : Opens X) (_ : x ∈ V) (hVU : V ≤ U), ∀ (y : X) (hy : y ∈ V), pres U y (hVU hy) p = 0
  /-- Every element of `A x` comes from a polynomial over some neighbourhood of `x`. -/
  pres_surjective (x : X) (a : obj x) :
    ∃ (V : Opens X) (hxV : x ∈ V) (p : MvPolynomial (Fin r) (X.presheaf.obj (op V))),
      pres V x hxV p = a

namespace StalkPresentation

variable {X : RingedSpace.{u}} {r : ℕ} (D : StalkPresentation X r)

section Sections

/-- The sections of the sheaf presented by `D` over an open `U`: families `(s x)_{x ∈ U}` which are
locally given by a polynomial with coefficients in the structure sheaf. -/
def Sections (U : Opens X) : Subring (∀ x : U, D.obj x) where
  carrier := {s | ∀ x : U, ∃ (V : Opens X) (hxV : (x : X) ∈ V) (hVU : V ≤ U)
      (p : MvPolynomial (Fin r) (X.presheaf.obj (op V))),
      ∀ (y : X) (hy : y ∈ V), s ⟨y, hVU hy⟩ = D.pres V y hy p}
  zero_mem' x := ⟨U, x.2, le_rfl, 0, fun _ _ => by simp⟩
  one_mem' x := ⟨U, x.2, le_rfl, 1, fun _ _ => by simp⟩
  add_mem' {s t} hs ht x := by
    obtain ⟨V₁, hx₁, hle₁, p, hp⟩ := hs x
    obtain ⟨V₂, hx₂, _, q, hq⟩ := ht x
    refine ⟨V₁ ⊓ V₂, ⟨hx₁, hx₂⟩, le_trans inf_le_left hle₁,
      MvPolynomial.map (X.presheaf.map (homOfLE (inf_le_left (a := V₁) (b := V₂))).op).hom p
        + MvPolynomial.map (X.presheaf.map (homOfLE (inf_le_right (a := V₁) (b := V₂))).op).hom q,
      fun y hy => ?_⟩
    rw [map_add, ← D.pres_res (inf_le_left (a := V₁) (b := V₂)) y hy p,
      ← D.pres_res (inf_le_right (a := V₁) (b := V₂)) y hy q, ← hp y hy.1, ← hq y hy.2]
    rfl
  mul_mem' {s t} hs ht x := by
    obtain ⟨V₁, hx₁, hle₁, p, hp⟩ := hs x
    obtain ⟨V₂, hx₂, _, q, hq⟩ := ht x
    refine ⟨V₁ ⊓ V₂, ⟨hx₁, hx₂⟩, le_trans inf_le_left hle₁,
      MvPolynomial.map (X.presheaf.map (homOfLE (inf_le_left (a := V₁) (b := V₂))).op).hom p
        * MvPolynomial.map (X.presheaf.map (homOfLE (inf_le_right (a := V₁) (b := V₂))).op).hom q,
      fun y hy => ?_⟩
    rw [map_mul, ← D.pres_res (inf_le_left (a := V₁) (b := V₂)) y hy p,
      ← D.pres_res (inf_le_right (a := V₁) (b := V₂)) y hy q, ← hp y hy.1, ← hq y hy.2]
    rfl
  neg_mem' {s} hs x := by
    obtain ⟨V, hxV, hle, p, hp⟩ := hs x
    refine ⟨V, hxV, hle, -p, fun y hy => ?_⟩
    rw [map_neg, ← hp y hy]
    rfl

/-- Restriction of sections along an inclusion of opens. -/
def restrictHom {U V : Opens X} (hUV : U ≤ V) : D.Sections V →+* D.Sections U where
  toFun s := ⟨fun x => s.1 ⟨x, hUV x.2⟩, by
    intro x
    obtain ⟨W, hxW, hle, p, hp⟩ := s.2 ⟨x, hUV x.2⟩
    exact ⟨W ⊓ U, ⟨hxW, x.2⟩, inf_le_right,
      MvPolynomial.map (X.presheaf.map (homOfLE (inf_le_left (a := W) (b := U))).op).hom p,
      fun y hy => by
        rw [← D.pres_res (inf_le_left (a := W) (b := U)) y hy p]
        exact hp y hy.1⟩⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The restriction of a section `s` to `U` takes the value of `s` at each point of `U`. -/
@[simp]
theorem restrictHom_coe {U V : Opens X} (hUV : U ≤ V) (s : D.Sections V) (x : U) :
    (D.restrictHom hUV s).1 x = s.1 ⟨x, hUV x.2⟩ := rfl

/-- The presheaf of commutative rings presented by `D`. -/
def presheaf : TopCat.Presheaf CommRingCat.{u} X where
  obj U := CommRingCat.of (D.Sections U.unop)
  map i := CommRingCat.ofHom (D.restrictHom (leOfHom i.unop))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The restriction map of `D.presheaf` takes the value of a section at each point of the smaller
open. -/
@[simp]
theorem presheaf_map_coe {U V : Opens X} (i : op V ⟶ op U) (s : D.presheaf.obj (op V))
    (x : U) : (D.presheaf.map i s).1 x = s.1 ⟨x, i.unop.le x.2⟩ := rfl

/-- Two sections of `D.presheaf` over `U` are equal if they agree at every point of `U`. -/
theorem presheaf_ext {U : Opens X} {s t : D.presheaf.obj (op U)}
    (h : ∀ x : U, s.1 x = t.1 x) : s = t := Subtype.ext (funext h)

/-- Equal sections of `D` over `U` have equal values at every point of `U`. -/
private theorem sections_congr {U : Opens X} {s t : D.Sections U} (h : s = t) (x : U) :
    s.1 x = t.1 x := congrFun (congrArg Subtype.val h) x

/-- The sheaf of commutative rings presented by `D` is indeed a sheaf: its sections are the
families of elements of the `A x` satisfying a local condition, so they glue uniquely. -/
theorem isSheaf : D.presheaf.IsSheaf := by
  classical
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hcompat
  have key : ∀ (i j : ι) (y : X) (hi : y ∈ U i) (hj : y ∈ U j),
      (sf i).1 ⟨y, hi⟩ = (sf j).1 ⟨y, hj⟩ := fun i j y hi hj =>
    D.sections_congr (hcompat i j) ⟨y, ⟨hi, hj⟩⟩
  have hmem : ∀ x : (iSup U : Opens X), ∃ i, (x : X) ∈ U i := fun x => Opens.mem_iSup.mp x.2
  refine ⟨⟨fun x => (sf (hmem x).choose).1 ⟨x, (hmem x).choose_spec⟩, fun x => ?_⟩,
    fun i => ?_, fun s hs => ?_⟩
  · obtain ⟨V, hxV, hle, p, hp⟩ := (sf (hmem x).choose).2 ⟨x, (hmem x).choose_spec⟩
    refine ⟨V, hxV, le_trans hle (le_iSup U _), p, fun y hy => ?_⟩
    rw [← hp y hy]
    exact key _ _ y _ _
  · exact presheaf_ext D fun y => key _ _ (y : X) _ _
  · exact presheaf_ext D fun x =>
      D.sections_congr (hs (hmem x).choose) ⟨(x : X), (hmem x).choose_spec⟩

/-- The sheaf of commutative rings presented by `D`. -/
def sheaf : TopCat.Sheaf CommRingCat.{u} X := ⟨D.presheaf, D.isSheaf⟩

/-- The underlying presheaf of `D.sheaf` is `D.presheaf`. -/
@[simp]
theorem sheaf_presheaf : D.sheaf.presheaf = D.presheaf := rfl

end Sections

section OfSections

/-- The section of the sheaf over `U` determined by a polynomial with coefficients in `O_X(U)`. -/
noncomputable def ofSections (U : Opens X) :
    MvPolynomial (Fin r) (X.presheaf.obj (op U)) →+* D.Sections U where
  toFun p := ⟨fun x => D.pres U x x.2 p, fun x => ⟨U, x.2, le_rfl, p, fun _ _ => rfl⟩⟩
  map_one' := Subtype.ext (funext fun _ => map_one _)
  map_mul' _ _ := Subtype.ext (funext fun _ => map_mul _ _ _)
  map_zero' := Subtype.ext (funext fun _ => map_zero _)
  map_add' _ _ := Subtype.ext (funext fun _ => map_add _ _ _)

/-- The section determined by `p` takes the value `D.pres U x _ p` at each point `x` of `U`. -/
@[simp]
theorem ofSections_coe (U : Opens X) (p : MvPolynomial (Fin r) (X.presheaf.obj (op U)))
    (x : U) : (D.ofSections U p).1 x = D.pres U x x.2 p := rfl

/-- The presentation maps are compatible with restriction. -/
theorem restrictHom_ofSections {U V : Opens X} (hUV : U ≤ V)
    (p : MvPolynomial (Fin r) (X.presheaf.obj (op V))) :
    D.restrictHom hUV (D.ofSections V p)
      = D.ofSections U (MvPolynomial.map (X.presheaf.map (homOfLE hUV).op).hom p) :=
  Subtype.ext (funext fun x => D.pres_res hUV x x.2 p)

/-- Every section is, locally, in the image of the presentation map. -/
theorem exists_ofSections (U : Opens X) (s : D.Sections U) (x : X) (hx : x ∈ U) :
    ∃ (V : Opens X) (_ : x ∈ V) (hVU : V ≤ U)
      (p : MvPolynomial (Fin r) (X.presheaf.obj (op V))),
      D.ofSections V p = D.restrictHom hVU s := by
  obtain ⟨V, hxV, hVU, p, hp⟩ := s.2 ⟨x, hx⟩
  exact ⟨V, hxV, hVU, p, Subtype.ext (funext fun y => (hp y y.2).symm)⟩

/-- A section coming from a polynomial vanishes exactly when the polynomial presents `0` at every
point. -/
theorem ofSections_eq_zero_iff (U : Opens X)
    (p : MvPolynomial (Fin r) (X.presheaf.obj (op U))) :
    D.ofSections U p = 0 ↔ ∀ (x : X) (hx : x ∈ U), D.pres U x hx p = 0 :=
  ⟨fun h x hx => D.sections_congr h ⟨x, hx⟩,
    fun h => Subtype.ext (funext fun x => h x x.2)⟩

end OfSections

section Stalk

/-- Evaluation of a section at a point of its domain. -/
def evalHom (U : Opens X) (x : X) (hx : x ∈ U) : D.presheaf.obj (op U) ⟶ D.obj x :=
  CommRingCat.ofHom ((Pi.evalRingHom (fun y : U => (D.obj y : Type u)) ⟨x, hx⟩).comp
    (D.Sections U).subtype)

/-- Evaluation at `x` sends a section `s` to its value `s x`. -/
@[simp]
theorem evalHom_apply (U : Opens X) (x : X) (hx : x ∈ U) (s : D.presheaf.obj (op U)) :
    D.evalHom U x hx s = s.1 ⟨x, hx⟩ := rfl

/-- Evaluation at `x` as a cocone on the diagram computing the stalk at `x`. -/
def evalCocone (x : X) : Cocone ((OpenNhds.inclusion x).op ⋙ D.presheaf) where
  pt := D.obj x
  ι := { app := fun U => D.evalHom U.unop.1 x U.unop.2
         naturality := fun _ _ _ => rfl }

/-- The canonical map from the stalk of the presented sheaf at `x` to `A x`, given by evaluating a
germ at `x`. -/
noncomputable def stalkDesc (x : X) : D.presheaf.stalk x ⟶ D.obj x :=
  colimit.desc _ (D.evalCocone x)

/-- The map `stalkDesc x` sends the germ at `x` of a section `s` to its value `s x`. -/
@[simp]
theorem stalkDesc_germ (U : Opens X) (x : X) (hx : x ∈ U) (s : D.presheaf.obj (op U)) :
    D.stalkDesc x (D.presheaf.germ U x hx s) = s.1 ⟨x, hx⟩ :=
  ConcreteCategory.congr_hom
    (colimit.ι_desc (D.evalCocone x) (op (⟨U, hx⟩ : OpenNhds x))) s

/-- The map from the stalk at `x` to `A x` is surjective. -/
theorem stalkDesc_surjective (x : X) : Function.Surjective (D.stalkDesc x) := by
  intro a
  obtain ⟨V, hxV, p, hp⟩ := D.pres_surjective x a
  exact ⟨D.presheaf.germ V x hxV (D.ofSections V p),
    (D.stalkDesc_germ V x hxV (D.ofSections V p)).trans hp⟩

/-- The map from the stalk at `x` to `A x` is injective. -/
theorem stalkDesc_injective (x : X) : Function.Injective (D.stalkDesc x) := by
  rw [injective_iff_map_eq_zero]
  intro t ht
  obtain ⟨U, hx, s, rfl⟩ := D.presheaf.exists_germ_eq t
  have ht' : s.1 ⟨x, hx⟩ = 0 := (D.stalkDesc_germ U x hx s).symm.trans ht
  obtain ⟨V, hxV, hVU, p, hp⟩ := D.exists_ofSections U s x hx
  have hp0 : D.pres V x hxV p = 0 :=
    (D.sections_congr hp ⟨x, hxV⟩).trans ht'
  obtain ⟨W, hxW, hWV, hW⟩ := D.pres_eq_zero_nhds V x hxV p hp0
  have hres : D.presheaf.map (homOfLE (hWV.trans hVU)).op s = 0 :=
    presheaf_ext D fun y =>
      (D.sections_congr hp ⟨(y : X), hWV y.2⟩).symm.trans (hW y y.2)
  rw [← TopCat.Presheaf.germ_res_apply D.presheaf (homOfLE (hWV.trans hVU)) x hxW s, hres,
    map_zero]

/-- The map from the stalk at `x` to `A x` is bijective. -/
theorem stalkDesc_bijective (x : X) : Function.Bijective (D.stalkDesc x) :=
  ⟨D.stalkDesc_injective x, D.stalkDesc_surjective x⟩

/-- The map from the stalk at `x` to `A x` is an isomorphism of commutative rings. -/
instance isIso_stalkDesc (x : X) : IsIso (D.stalkDesc x) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr (D.stalkDesc_bijective x)

/-- The identification of the stalk at `x` of the presented sheaf with `A x`, as an isomorphism of
commutative rings. Its forward map is evaluation of a germ at `x`. -/
noncomputable def stalkIso (x : X) : D.presheaf.stalk x ≅ D.obj x := asIso (D.stalkDesc x)

/-- The forward map of `stalkIso x` is `stalkDesc x`. -/
@[simp]
theorem stalkIso_hom (x : X) : (D.stalkIso x).hom = D.stalkDesc x := rfl

/-- The isomorphism `stalkIso x` sends the germ at `x` of a section `s` to its value `s x`. -/
@[simp]
theorem stalkIso_hom_germ (U : Opens X) (x : X) (hx : x ∈ U) (s : D.presheaf.obj (op U)) :
    (D.stalkIso x).hom (D.presheaf.germ U x hx s) = s.1 ⟨x, hx⟩ :=
  D.stalkDesc_germ U x hx s

/-- The forward map of `stalkIso x` is a left inverse of its inverse. -/
@[simp]
theorem stalkIso_hom_inv_apply (x : X) (a : D.obj x) :
    (D.stalkIso x).hom ((D.stalkIso x).inv a) = a :=
  (D.stalkIso x).inv_hom_id_apply a

end Stalk

/-- A morphism of stalk presentations: a ring homomorphism at each point compatible with the
presentation maps. -/
structure Hom (D E : StalkPresentation X r) where
  /-- The map on the ring attached to each point. -/
  app (x : X) : D.obj x ⟶ E.obj x
  /-- Compatibility with the presentation maps. -/
  app_pres (U : Opens X) (x : X) (hx : x ∈ U)
    (p : MvPolynomial (Fin r) (X.presheaf.obj (op U))) :
    (app x) (D.pres U x hx p) = E.pres U x hx p

namespace Hom

variable {D} {E : StalkPresentation X r} (φ : D.Hom E)

/-- The morphism of sheaves induced by a morphism of presentations. -/
def sheafHom : D.presheaf ⟶ E.presheaf where
  app U := CommRingCat.ofHom
    { toFun := fun s => ⟨fun x => φ.app x (s.1 x), by
        intro x
        obtain ⟨V, hxV, hVU, p, hp⟩ := s.2 x
        refine ⟨V, hxV, hVU, p, fun y hy => ?_⟩
        change φ.app y (s.1 ⟨y, hVU hy⟩) = E.pres V y hy p
        rw [hp y hy, φ.app_pres]⟩
      map_one' := Subtype.ext (funext fun _ => map_one _)
      map_mul' := fun _ _ => Subtype.ext (funext fun _ => map_mul _ _ _)
      map_zero' := Subtype.ext (funext fun _ => map_zero _)
      map_add' := fun _ _ => Subtype.ext (funext fun _ => map_add _ _ _) }
  naturality _ _ _ := rfl

/-- The morphism induced by `φ` acts on a section pointwise by `φ.app`. -/
@[simp]
theorem sheafHom_app_coe (U : Opens X) (s : D.presheaf.obj (op U)) (x : U) :
    ((φ.sheafHom.app (op U)) s).1 x = φ.app x (s.1 x) := rfl

/-- The induced morphism of sheaves, as a morphism of sheaves of commutative rings. -/
def sheafMap : D.sheaf ⟶ E.sheaf := ⟨φ.sheafHom⟩

/-- The underlying morphism of presheaves of `φ.sheafMap` is `φ.sheafHom`. -/
@[simp]
theorem sheafMap_hom : φ.sheafMap.hom = φ.sheafHom := rfl

/-- The morphism of sheaves induced by `φ` sends the section presented by `p` to the section
presented by `p`. -/
theorem sheafHom_ofSections (U : Opens X) (p : MvPolynomial (Fin r) (X.presheaf.obj (op U))) :
    (φ.sheafHom.app (op U)) (D.ofSections U p) = E.ofSections U p :=
  Subtype.ext (funext fun x => φ.app_pres U x x.2 p)

/-- The morphism of sheaves induced by `φ` acts on a section pointwise by `φ.app`. -/
@[simp]
theorem sheafMap_hom_app_coe (U : Opens X) (s : D.sheaf.presheaf.obj (op U)) (x : U) :
    ((φ.sheafMap.hom.app (op U)) s).1 x = φ.app x (s.1 x) := rfl

/-- The induced morphism of sheaves sends the section presented by `p` to the section presented
by `p`. -/
theorem sheafMap_hom_app_ofSections (U : Opens X)
    (p : MvPolynomial (Fin r) (X.presheaf.obj (op U))) :
    (φ.sheafMap.hom.app (op U)) (D.ofSections U p) = E.ofSections U p :=
  φ.sheafHom_ofSections U p

/-- Under the identifications of stalks with the rings `A x`, the stalk map at `x` of the morphism
induced by `φ` is `φ.app x`. -/
theorem stalkIso_hom_stalkFunctor_map (x : X) (t : D.presheaf.stalk x) :
    (E.stalkIso x).hom ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map φ.sheafHom t)
      = φ.app x ((D.stalkIso x).hom t) := by
  obtain ⟨U, hx, s, rfl⟩ := D.presheaf.exists_germ_eq t
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, stalkIso_hom_germ, stalkIso_hom_germ,
    sheafHom_app_coe]

end Hom

end StalkPresentation

end Stacks.AlgebraicGeometry.QuasiRegular
