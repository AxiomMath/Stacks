module

public import Mathlib.CategoryTheory.Sites.Over
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.LocalTriviality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.PseudoTorsors
import StacksCore.Tactic.StacksAttribute

/-!
# The category of torsors under a sheaf of groups

Let `(C, J)` be a site and let `𝒢` be a sheaf of (possibly non-commutative) groups on `C`. For
an object `U` of `C` write `𝒢|_U` for the restriction of `𝒢` to the localized site `C/U`. The
category `𝒢-Torsors` has as objects the pairs `(U, F)` with `U` an object of `C` and `F` a
`𝒢|_U`-torsor in the sense of Stacks 03AH, and as morphisms `(U, F) ⟶ (V, H)` the pairs
`(f, α)` with `f : U ⟶ V` a morphism of `C` and `α : f^{-1}H ⟶ F` an isomorphism of
`𝒢|_U`-torsors. Sending `(U, F)` to `U` is a functor `p : 𝒢-Torsors ⥤ C`, and this is how
`𝒢-Torsors` is regarded as a category over `C`; the fibre category over `U` is the category of
`𝒢|_U`-torsors, which is a groupoid.

## Main definitions

* `SheafOfGroups.Torsors`: the objects of `𝒢-Torsors`.
* `SheafOfGroups.Torsors.Total`, with its restriction maps `totalMap` and its action
  `totalSmul`: the sheaf on `C` attached to the torsor of an object.
* `SheafOfGroups.Torsors.Hom`, the morphisms of `𝒢-Torsors`, and
  `SheafOfGroups.Torsors.instCategory`, the category they form.
* `SheafOfGroups.Torsors.projection`: the functor `p : 𝒢-Torsors ⥤ C`.

## Main results

* `SheafOfGroups.Torsors.isIso_of_isIso_base`: a morphism of `𝒢-Torsors` lying over an
  isomorphism of `C` is an isomorphism. In particular every morphism of a fibre category lies
  over an identity and is therefore invertible, which is the assertion that the fibre categories
  are groupoids.

## Implementation notes

The restriction `𝒢|_U` is `SheafOfGroups.over`, taken from
`StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.LocalTriviality`: the composite of `𝒢`
with `CategoryTheory.Over.forget`, so that the sections of `𝒢|_U` over an object `a : V ⟶ U`
of `C/U` are *by definition* the sections of `𝒢` over `V`; that it is again a sheaf is
`CategoryTheory.GrothendieckTopology.overPullback`. With
this model one and the same group of sections acts on the torsors of all the localized sites at
once, which is what lets the equivariance conditions below be stated for `𝒢` itself.

A torsor and its torsor condition are literally `PseudoTorsor` and `PseudoTorsor.IsTorsor` of
Stacks 03AH for the localized site `C/U`.

The isomorphism `α : f^{-1}H ⟶ F` of a morphism is recorded on the *total spaces*
`Total T V = Σ a : V ⟶ U, F(V, a)`: this is the sheaf on `C` corresponding to `F` under the
equivalence between sheaves on `C/U` and sheaves on `C` over `U`, and it is the presentation used
for the quotient stack of Stacks 0371
(`AlgebraicGeometry.AbstractGroupQuotientStack`). Its advantage is that the type of the recorded
map does not depend on `f`, so composition of morphisms is strictly associative and no coherence
isomorphisms for the functors `f^{-1}` are needed. Concretely a morphism records the inverse
`α⁻¹ : F ⟶ f^{-1}H` of the source's `α` as a map of sheaves `Total F ⟶ Total H` over `f` which
restricts to a bijection from the fibre of `Total F` over each `a : V ⟶ U` to the fibre of
`Total H` over `a ≫ f`; since the fibre of `Total H` over `a ≫ f` is the set of sections of
`f^{-1}H` over `(V, a)`, such a map is exactly an isomorphism `F ⟶ f^{-1}H` of sheaves on `C/U`,
and giving it is the same as giving `α`.

The group acting is `𝒢` rather than `𝒢|_U` in the equivariance condition, which is no change of
notion: the sections of `𝒢|_U` over `(V, a)` are the sections of `𝒢` over `V` by definition, and
likewise for `𝒢|_V` on the target side, so the displayed condition is `𝒢|_U`-equivariance
read through those identifications.

The universe of the sections of a torsor is independent of the universe of the sections of `𝒢`,
as it is for `PseudoTorsor`.

## References

* [Stacks Project, Tag 04UJ](https://stacks.math.columbia.edu/tag/04UJ)
* [Stacks Project, Tag 03AH](https://stacks.math.columbia.edu/tag/03AH)
-/

@[expose] public section

open CategoryTheory Opposite

universe t w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- **Stacks 04UJ.** An object of the category `𝒢-Torsors` of torsors under a sheaf of groups
`𝒢` on a site `(C, J)`: an object `U` of `C` together with a `𝒢|_U`-torsor on the localized
site `C/U`. -/
@[stacks 04UJ "the objects of 𝒢-Torsors", sga "1 XIII 1.3" "partial"]
structure SheafOfGroups.Torsors (𝒢 : SheafOfGroups.{w} (C := C) J) where
  /-- The object of `C` over which the pair lives. -/
  base : C
  /-- The sheaf on `C/U` with its action of `𝒢|_U`. -/
  torsor : PseudoTorsor.{t} (𝒢.over base)
  /-- The action turns the sheaf into a torsor, that is, it is locally nonempty. -/
  isTorsor : torsor.IsTorsor

namespace SheafOfGroups.Torsors

variable {𝒢 : SheafOfGroups.{w} (C := C) J}

/-- The total space of the torsor of an object of `𝒢-Torsors`: the sheaf on `C` whose sections
over `V` are the pairs of a morphism `a : V ⟶ U` and a section of the torsor over `(V, a)`. -/
def Total (T : Torsors.{t} 𝒢) (V : Cᵒᵖ) :=
  Σ a : V.unop ⟶ T.base, T.torsor.presheaf.obj (op (Over.mk a))

/-- The restriction maps of the total space of the torsor of an object of `𝒢-Torsors`. -/
def totalMap (T : Torsors.{t} 𝒢) {V W : Cᵒᵖ} (h : V ⟶ W) (p : T.Total V) : T.Total W :=
  ⟨h.unop ≫ p.1, T.torsor.presheaf.map
    (Over.homMk h.unop : Over.mk (h.unop ≫ p.1) ⟶ Over.mk p.1).op p.2⟩

/-- The base component of a restricted section of the total space. -/
@[simp]
theorem totalMap_fst (T : Torsors.{t} 𝒢) {V W : Cᵒᵖ} (h : V ⟶ W) (p : T.Total V) :
    (T.totalMap h p).1 = h.unop ≫ p.1 :=
  rfl

/-- The action of `𝒢` on the total space of the torsor of an object of `𝒢-Torsors`, through the
identification of the sections of `𝒢|_U` over `(V, a)` with the sections of `𝒢` over `V`. -/
def totalSmul (T : Torsors.{t} 𝒢) {V : Cᵒᵖ} (γ : 𝒢.presheaf.obj V) (p : T.Total V) :
    T.Total V :=
  ⟨p.1, T.torsor.act (op (Over.mk p.1)) γ p.2⟩

/-- The action on the total space does not move the base component. -/
@[simp]
theorem totalSmul_fst (T : Torsors.{t} 𝒢) {V : Cᵒᵖ} (γ : 𝒢.presheaf.obj V) (p : T.Total V) :
    (T.totalSmul γ p).1 = p.1 :=
  rfl

/-- **Stacks 04UJ.** A morphism `(U, F) ⟶ (V, H)` of the category `𝒢-Torsors`: a morphism
`f : U ⟶ V` of `C` together with an isomorphism `α : f^{-1}H ⟶ F` of `𝒢|_U`-torsors. The
isomorphism is recorded through its inverse on total spaces: a map of sheaves on `C` over `f`
which restricts to a bijection from the fibre of `Total F` over each `a : V ⟶ U` to the fibre
of `Total H` over `a ≫ f`. -/
@[stacks 04UJ "the morphisms of 𝒢-Torsors", sga "1 XIII 1.3" "partial"]
structure Hom (T T' : Torsors.{t} 𝒢) where
  /-- The morphism `f : U ⟶ V` of `C`. -/
  base : T.base ⟶ T'.base
  /-- The isomorphism `α⁻¹`, read on total spaces. -/
  map : ∀ V : Cᵒᵖ, T.Total V → T'.Total V
  /-- `α` is a map of sheaves, that is, it is compatible with the restriction maps. -/
  map_naturality : ∀ {V W : Cᵒᵖ} (h : V ⟶ W) (p : T.Total V),
    map W (T.totalMap h p) = T'.totalMap h (map V p)
  /-- `α` is equivariant for the action of `𝒢`. -/
  map_equivariant : ∀ (V : Cᵒᵖ) (γ : 𝒢.presheaf.obj V) (p : T.Total V),
    map V (T.totalSmul γ p) = T'.totalSmul γ (map V p)
  /-- `α` is an isomorphism `f^{-1}H ⟶ F`: over every `a : V ⟶ U` the recorded map is a
  bijection from the sections of `F` over `(V, a)` to the sections of `H` over `(V, a ≫ f)`. -/
  bijOn_map : ∀ (V : Cᵒᵖ) (a : V.unop ⟶ T.base),
    Set.BijOn (map V) {p : T.Total V | p.1 = a} {q : T'.Total V | q.1 = a ≫ base}

/-- Two morphisms of `𝒢-Torsors` with the same `f` and the same `α` are equal. -/
@[ext]
theorem Hom.ext {T T' : Torsors.{t} 𝒢} {m m' : Hom T T'} (hbase : m.base = m'.base)
    (hmap : m.map = m'.map) : m = m' := by
  cases m; cases m'; subst hbase; subst hmap; rfl

/-- The recorded map of a morphism of `𝒢-Torsors` lies over `f`: it sends a section of `F` over
`a` to a section of `H` over `a ≫ f`. -/
theorem Hom.fst_map {T T' : Torsors.{t} 𝒢} (m : Hom T T') {V : Cᵒᵖ} (p : T.Total V) :
    (m.map V p).1 = p.1 ≫ m.base :=
  (m.bijOn_map V p.1).mapsTo rfl

/-- A section of the target torsor over `a ≫ f` has a unique preimage over `a`. -/
theorem Hom.existsUnique_map {T T' : Torsors.{t} 𝒢} (m : Hom T T') {V : Cᵒᵖ}
    (a : V.unop ⟶ T.base) (q : T'.Total V) (hq : q.1 = a ≫ m.base) :
    ∃! p : T.Total V, p.1 = a ∧ m.map V p = q := by
  obtain ⟨p, hp, hpq⟩ := (m.bijOn_map V a).surjOn hq
  refine ⟨p, ⟨hp, hpq⟩, ?_⟩
  intro p' hp'
  exact (m.bijOn_map V a).injOn hp'.1 hp (hp'.2.trans hpq.symm)

/-- The identity morphism of an object of `𝒢-Torsors`. -/
def Hom.id (T : Torsors.{t} 𝒢) : Hom T T where
  base := 𝟙 T.base
  map := fun _ p => p
  map_naturality := fun _ _ => rfl
  map_equivariant := fun _ _ _ => rfl
  bijOn_map := fun _ a => by
    simp only [Category.comp_id]
    exact Set.bijOn_id _

/-- The composition of two morphisms of `𝒢-Torsors`. -/
def Hom.comp {T T' T'' : Torsors.{t} 𝒢} (m : Hom T T') (m' : Hom T' T'') : Hom T T'' where
  base := m.base ≫ m'.base
  map := fun V => m'.map V ∘ m.map V
  map_naturality := fun h p => by
    simp only [Function.comp_apply]
    rw [m.map_naturality, m'.map_naturality]
  map_equivariant := fun V γ p => by
    simp only [Function.comp_apply]
    rw [m.map_equivariant, m'.map_equivariant]
  bijOn_map := fun V a => by
    rw [← Category.assoc]
    exact (m'.bijOn_map V (a ≫ m.base)).comp (m.bijOn_map V a)

/-- **Stacks 04UJ.** The torsors under a sheaf of groups `𝒢` on a site `(C, J)` form a category
`𝒢-Torsors`: morphisms compose by composing `f` and `α`. -/
@[stacks 04UJ "the category 𝒢-Torsors", sga "1 XIII 1.3" "partial"]
instance instCategory : Category (Torsors.{t} 𝒢) where
  Hom T T' := Hom T T'
  id T := Hom.id T
  comp m m' := Hom.comp m m'
  id_comp _ := Hom.ext (Category.id_comp _) rfl
  comp_id _ := Hom.ext (Category.comp_id _) rfl
  assoc _ _ _ := Hom.ext (Category.assoc _ _ _) rfl

/-- **Stacks 04UJ.** The functor `p : 𝒢-Torsors ⥤ C` sending a pair `(U, F)` to `U`, which is
how `𝒢-Torsors` is regarded as a category over the site. -/
@[stacks 04UJ "the functor p to the site", sga "1 XIII 1.3" "partial"]
def projection : Torsors.{t} 𝒢 ⥤ C where
  obj T := T.base
  map m := Hom.base m

/-- The functor `p` sends a morphism of `𝒢-Torsors` to its morphism `f` of `C`. -/
@[simp]
theorem projection_map {T T' : Torsors.{t} 𝒢} (m : T ⟶ T') :
    projection.map m = Hom.base m :=
  rfl

section Inverse

variable {T T' : Torsors.{t} 𝒢} (m : T ⟶ T') [IsIso (Hom.base m)]

/-- A section of the target torsor over `b` has a unique preimage over `b ≫ f⁻¹`. -/
private theorem existsUnique_invMap (V : Cᵒᵖ) (q : T'.Total V) :
    ∃! p : T.Total V, p.1 = q.1 ≫ inv (Hom.base m) ∧ m.map V p = q :=
  m.existsUnique_map (q.1 ≫ inv (Hom.base m)) q (by simp)

/-- The map on total spaces inverse to that of a morphism of `𝒢-Torsors` whose morphism `f` is
an isomorphism: a section of the target torsor over `b` has a unique preimage over
`b ≫ f⁻¹`. -/
private noncomputable def invMap (V : Cᵒᵖ) (q : T'.Total V) : T.Total V :=
  (existsUnique_invMap m V q).exists.choose

private theorem invMap_fst (V : Cᵒᵖ) (q : T'.Total V) :
    (invMap m V q).1 = q.1 ≫ inv (Hom.base m) :=
  (existsUnique_invMap m V q).exists.choose_spec.1

@[simp]
private theorem map_invMap (V : Cᵒᵖ) (q : T'.Total V) : m.map V (invMap m V q) = q :=
  (existsUnique_invMap m V q).exists.choose_spec.2

private theorem invMap_eq {V : Cᵒᵖ} {q : T'.Total V} {p : T.Total V}
    (hp : p.1 = q.1 ≫ inv (Hom.base m)) (hpq : m.map V p = q) : p = invMap m V q :=
  ((existsUnique_invMap m V q).unique ⟨hp, hpq⟩
    ⟨invMap_fst m V q, map_invMap m V q⟩)

@[simp]
private theorem invMap_map (V : Cᵒᵖ) (p : T.Total V) : invMap m V (m.map V p) = p :=
  (invMap_eq m (by simp [m.fst_map p]) rfl).symm

/-- The inverse of a morphism of `𝒢-Torsors` whose morphism `f` is an isomorphism. -/
private noncomputable def homInv : T' ⟶ T where
  base := inv (Hom.base m)
  map := invMap m
  map_naturality := fun h q => by
    refine (invMap_eq m ?_ ?_).symm
    · rw [totalMap_fst, invMap_fst, totalMap_fst, Category.assoc]
    · rw [m.map_naturality, map_invMap]
  map_equivariant := fun V γ q => by
    refine (invMap_eq m ?_ ?_).symm
    · rw [totalSmul_fst, invMap_fst, totalSmul_fst]
    · rw [m.map_equivariant, map_invMap]
  bijOn_map := fun V b => by
    refine ⟨fun q hq => by simpa [invMap_fst] using congrArg (· ≫ inv (Hom.base m)) hq,
      fun q hq q' hq' h => ?_, fun p hp => ⟨m.map V p, ?_, invMap_map m V p⟩⟩
    · rw [← map_invMap m V q, ← map_invMap m V q', h]
    · rw [Set.mem_ofPred_eq, m.fst_map p, hp, Category.assoc, IsIso.inv_hom_id,
        Category.comp_id]

/-- **Stacks 04UJ.** A morphism of `𝒢-Torsors` whose morphism `f` of the site is an isomorphism
is itself an isomorphism. Every morphism of a fibre category of `p : 𝒢-Torsors ⥤ C` lies over an
identity, so this says that the fibre category over `U` — the category of `𝒢|_U`-torsors — is a
groupoid. -/
@[stacks 04UJ "the fibre categories are groupoids"]
theorem isIso_of_isIso_base : IsIso m :=
  ⟨homInv m, Hom.ext (IsIso.hom_inv_id _) (by funext V p; exact invMap_map m V p),
    Hom.ext (IsIso.inv_hom_id _) (by funext V q; exact map_invMap m V q)⟩

end Inverse

end SheafOfGroups.Torsors

end
