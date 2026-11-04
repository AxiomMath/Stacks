module

public import StacksFrontier.AlgebraicGeometry.LimitIndexUniverseIntegral.Basic

/-!
# Descent of a vanishing section at a free index universe, for affine stages

Mathlib's `AlgebraicGeometry.exists_appTop_map_eq_zero_of_isAffine_of_isLimit` says that in a
cofiltered limit of affine schemes a global section of one stage which vanishes in the limit
already vanishes at some later stage.  Its proof identifies `Γ` of the limit with the filtered
colimit of the `Γ`s, which needs the colimit of the stage rings to exist in the schemes' own
universe — so the statement is available only with the index category in that universe.

This file proves the same descent, **up to a power and with the index universe free**, from the
algebra of `StacksFrontier/AlgebraicGeometry/LimitIndexUniverseIntegral/Basic.lean`.  Two things are
traded for the smallness:

* the transition morphisms are assumed **finite**, not merely affine — which is what Tag 09ZN
  assumes and Tag 09ZM does not, and which is what makes each stage ring integral over an
  earlier one;
* the conclusion is weakened from `s = 0` at a later stage to `s ^ n = 0` at a later stage, which
  is all Tag 09ZN's use of it needs, a power of a monic polynomial being monic.

The bridge from the geometry to the algebra is `isSmallColimit_appTop`: for a limit cone of
affine schemes with affine vertex, `Γ` of the vertex has the universal property of the colimit of
the `Γ`s **among rings in the schemes' universe**, with no smallness used and no colimit formed.
It is the `Spec`/`Γ` equivalence of affine schemes and nothing else: a compatible family of ring
maps to `C` is exactly a cone with vertex `Spec C`, the limit cone factors it, and `Spec` is
fully faithful.

Nothing here carries the Tag 09ZN attribute.  Tag 09ZN is one unqualified assertion about a
system whose stages are *not* assumed affine; the reduction to affine stages is
[Stacks, Tag 09ZM], a separate tag, which is open at a free index universe.

## Main results

* `sectionsMap`, `sectionsCocone`: the directed system of global sections of the stages and the
  cocone on it induced by a cone of schemes.
* `isSmallColimit_appTop`: `Γ` of the vertex of a limit cone of affine schemes with affine vertex
  is universal among rings in the schemes' universe.
* `exists_pow_appTop_map_eq_zero`: a global section of a stage that vanishes in the limit has a
  power vanishing at a later stage — at a free index universe, with finite transitions.
* `exists_isFinite_of_isAffine`, `eventually_isFinite_of_isAffine`: **Tag 09ZN for affine stages
  over an affine base, at a free index universe and with no smallness hypothesis.**

## References

* [The Stacks Project, Tag 09ZN](https://stacks.math.columbia.edu/tag/09ZN)
-/

@[expose] public section

noncomputable section

universe w u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Stacks.IntegralLimitAffine

variable {I : Type w} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u})

/-- The transition map on global sections of an inverse system of schemes indexed by the opposite
of a preorder: for `i ≤ j` the transition morphism goes `Dⱼ ⟶ Dᵢ`, so on global sections it goes
`Γ(Dᵢ) ⟶ Γ(Dⱼ)`. -/
def sectionsMap (i j : I) (h : i ≤ j) : ↥Γ(D.obj (op i), ⊤) →+* ↥Γ(D.obj (op j), ⊤) :=
  (D.map (homOfLE h).op).appTop.hom

/-- `sectionsMap D i j h` is the map on global sections induced by the transition morphism. -/
@[simp] theorem sectionsMap_apply (i j : I) (h : i ≤ j) (x : ↥Γ(D.obj (op i), ⊤)) :
    sectionsMap D i j h x = (D.map (homOfLE h).op).appTop.hom x := rfl

/-- The transition map on global sections from a stage to itself is the identity. -/
theorem sectionsMap_self (i : I) (x : ↥Γ(D.obj (op i), ⊤)) :
    sectionsMap D i i le_rfl x = x := by
  rw [sectionsMap_apply, show (homOfLE (le_refl i)).op = 𝟙 _ from Subsingleton.elim _ _]
  simp

/-- The transition maps on global sections compose: for `i ≤ j ≤ k`, the map `Γ(Dᵢ) ⟶ Γ(Dⱼ)`
followed by `Γ(Dⱼ) ⟶ Γ(Dₖ)` is the map `Γ(Dᵢ) ⟶ Γ(Dₖ)`. -/
theorem sectionsMap_trans {i j k : I} (hij : i ≤ j) (hjk : j ≤ k)
    (x : ↥Γ(D.obj (op i), ⊤)) :
    sectionsMap D j k hjk (sectionsMap D i j hij x) = sectionsMap D i k (hij.trans hjk) x := by
  simp only [sectionsMap_apply]
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← D.map_comp,
    show (homOfLE hjk).op ≫ (homOfLE hij).op = (homOfLE (hij.trans hjk)).op from
      Subsingleton.elim _ _]

/-- The global sections of the stages, with the maps `sectionsMap`, form a directed system. -/
instance directedSystem_sectionsMap :
    DirectedSystem (fun i : I ↦ ↥Γ(D.obj (op i), ⊤)) fun i j h ↦ sectionsMap D i j h :=
  { map_self := fun ⦃i⦄ x ↦ sectionsMap_self D i x
    map_map := fun ⦃_ _ _⦄ hij hjk x ↦ sectionsMap_trans D hij hjk x }

/-- The cocone on the system of global sections induced by a cone of schemes. -/
def sectionsCocone (c : Cone D) (i : I) : ↥Γ(D.obj (op i), ⊤) →+* ↥Γ(c.pt, ⊤) :=
  (c.π.app (op i)).appTop.hom

/-- The maps `sectionsCocone D c` are compatible with the transition maps `sectionsMap D`. -/
theorem sectionsCocone_comp (c : Cone D) (i j : I) (h : i ≤ j) (x : ↥Γ(D.obj (op i), ⊤)) :
    sectionsCocone D c j (sectionsMap D i j h x) = sectionsCocone D c i x := by
  simp only [sectionsCocone, sectionsMap_apply]
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, c.w]

/-- The cone with vertex `Spec C` determined by a compatible family of ring maps out of the
global sections of the stages, when the stages are affine. -/
def specCone [∀ i, IsAffine (D.obj i)] (C : Type u) [CommRing C]
    (g : ∀ i : I, ↥Γ(D.obj (op i), ⊤) →+* C)
    (hg : ∀ (i j : I) (h : i ≤ j) (x : ↥Γ(D.obj (op i), ⊤)), g j (sectionsMap D i j h x) = g i x) :
    Cone D where
  pt := Spec (CommRingCat.of C)
  π :=
  { app := fun X ↦ Spec.map (CommRingCat.ofHom (g X.unop)) ≫ (D.obj X).isoSpec.inv
    naturality := fun X Y φ ↦ by
      have hφ : (homOfLE (leOfHom φ.unop)).op = φ := Subsingleton.elim _ _
      have hgφ : (D.map φ).appTop ≫ CommRingCat.ofHom (g X.unop)
          = CommRingCat.ofHom (g Y.unop) := by
        refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
        have hx := hg Y.unop X.unop (leOfHom φ.unop) x
        rw [sectionsMap_apply, hφ] at hx
        simpa using hx
      simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
      rw [Category.assoc, ← Scheme.isoSpec_inv_naturality (D.map φ), ← Category.assoc,
        ← Spec.map_comp, hgφ] }

/-- The leg of `specCone D C g hg` at `X` is `Spec` of `g` followed by the inverse of the
isomorphism of `D.obj X` with the spectrum of its global sections. -/
@[simp] theorem specCone_π_app [∀ i, IsAffine (D.obj i)] (C : Type u) [CommRing C]
    (g : ∀ i : I, ↥Γ(D.obj (op i), ⊤) →+* C)
    (hg : ∀ (i j : I) (h : i ≤ j) (x : ↥Γ(D.obj (op i), ⊤)), g j (sectionsMap D i j h x) = g i x)
    (X : Iᵒᵖ) :
    (specCone D C g hg).π.app X
      = Spec.map (CommRingCat.ofHom (g X.unop)) ≫ (D.obj X).isoSpec.inv := rfl

/-- If `c` is a limit cone of a system of affine schemes and its vertex is affine, then the cocone
on global sections is universal among commutative rings in the schemes' universe.

No smallness hypothesis is used and no colimit of rings is formed: a compatible family of ring
maps to `C` is exactly a cone with vertex `Spec C`, the limit cone factors it, and `Spec` is
fully faithful. -/
theorem isSmallColimit_appTop [∀ i, IsAffine (D.obj i)] (c : Cone D) (hc : IsLimit c)
    [IsAffine c.pt] :
    Stacks.IntegralLimitAlgebra.IsSmallColimit (fun i j h ↦ sectionsMap D i j h)
      (sectionsCocone D c) := by
  intro C _ g hg
  obtain ⟨m, hm⟩ : ∃ m : Spec (CommRingCat.of C) ⟶ c.pt,
      ∀ X, m ≫ c.π.app X = (specCone D C g hg).π.app X :=
    ⟨hc.lift (specCone D C g hg), fun X ↦ hc.fac _ X⟩
  refine ⟨(Spec.preimage (m ≫ c.pt.isoSpec.hom)).hom, fun i x ↦ ?_⟩
  have hkey : (c.π.app (op i)).appTop ≫ Spec.preimage (m ≫ c.pt.isoSpec.hom)
      = CommRingCat.ofHom (g i) := by
    refine Spec.map_injective ?_
    rw [Spec.map_comp, Spec.map_preimage, Category.assoc, Scheme.isoSpec_hom_naturality,
      ← Category.assoc, hm (op i), specCone_π_app]
    simp
  exact congrArg (fun φ : Γ(D.obj (op i), ⊤) ⟶ CommRingCat.of C ↦ φ.hom x) hkey

/-- Finite transition morphisms induce finite maps on global sections. -/
private theorem finite_sectionsMap [∀ i, IsAffine (D.obj i)]
    (hfinite : ∀ (i j : I) (h : i ≤ j), IsFinite (D.map (homOfLE h).op)) (a b : I) (h : a ≤ b) :
    (sectionsMap D a b h).Finite := by
  have := hfinite a b h
  exact (D.map (homOfLE h).op).finite_appTop

/-- **Descent of a vanishing section at a free index universe.**  Let `D` be an inverse system of
affine schemes indexed by the opposite of a nonempty directed preorder in an arbitrary universe,
with *finite* transition morphisms, and let `c` be a limit cone with affine vertex.  A global
section of one stage whose image in the limit vanishes has a positive power vanishing at some
later stage.

This is Mathlib's `exists_appTop_map_eq_zero_of_isAffine_of_isLimit` with the index universe
freed, at the cost of finite rather than affine transitions and of a power. -/
theorem exists_pow_appTop_map_eq_zero [IsDirectedOrder I] [Nonempty I]
    [∀ i, IsAffine (D.obj i)] (c : Cone D) (hc : IsLimit c) [IsAffine c.pt]
    (hfinite : ∀ (i j : I) (h : i ≤ j), IsFinite (D.map (homOfLE h).op))
    (i : I) (s : ↥Γ(D.obj (op i), ⊤)) (hs : (c.π.app (op i)).appTop.hom s = 0) :
    ∃ (j : I) (h : i ≤ j) (n : ℕ), 0 < n ∧ (D.map (homOfLE h).op).appTop.hom (s ^ n) = 0 := by
  exact Stacks.IntegralLimitAlgebra.exists_pow_eq_zero
    (fun a b hab ↦ sectionsMap D a b hab) (finite_sectionsMap D hfinite) (sectionsCocone_comp D c)
    (isSmallColimit_appTop D c hc) i s hs

/-- **[Stacks, Tag 09ZN] with affine stages, at an index universe independent of the scheme
universe and with no smallness hypothesis.**

Let `D` be an inverse system of affine schemes indexed by the opposite of a nonempty directed
preorder `I` in an arbitrary universe, over an affine base `S`, with finite transition morphisms
and structure morphisms locally of finite type.  Let `c` be a limit cone and let `f` be the
induced morphism to `S`.  If `f` is integral then `p j` is finite for some `j ≥ i₀`, for any
prescribed `i₀`.  (The vertex is then affine automatically, `f` being affine and `S` affine, so
no hypothesis on it is carried.)

Because the structure morphism at a later index factors through the transition morphism, and
finiteness is stable under composition, one such index gives finiteness at every later index; so
this is the full "for `i` large enough" of the source statement in the affine case.

The affineness of the stages is the only thing separating this from Tag 09ZN
itself: the source reduces to it by covering `S` with affine opens and invoking
[Stacks, Tag 09ZM] to make the structure morphisms affine, and Tag 09ZM is a separate tag which
is open at a free index universe. -/
theorem exists_isFinite_of_isAffine [IsDirectedOrder I] [Nonempty I]
    [∀ i, IsAffine (D.obj i)] {S : Scheme.{u}} [IsAffine S]
    (p : ∀ i : I, D.obj (op i) ⟶ S)
    (hp : ∀ (i j : I) (h : i ≤ j), p j = D.map (homOfLE h).op ≫ p i)
    (c : Cone D) (hc : IsLimit c) (f : c.pt ⟶ S) [IsIntegralHom f]
    (hf : ∀ i : I, f = c.π.app (op i) ≫ p i)
    (hfinite : ∀ (i j : I) (h : i ≤ j), IsFinite (D.map (homOfLE h).op))
    [∀ i : I, LocallyOfFiniteType (p i)] (i₀ : I) :
    ∃ (j : I) (_ : i₀ ≤ j), IsFinite (p j) := by
  have : IsAffine c.pt := isAffine_of_isAffineHom f
  have hr : ∀ (a b : I) (h : a ≤ b) (x : ↥Γ(S, ⊤)),
      sectionsMap D a b h ((p a).appTop.hom x) = (p b).appTop.hom x := by
    intro a b h x
    rw [sectionsMap_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← hp a b h]
  have hftype : ((p i₀).appTop.hom).FiniteType :=
    HasRingHomProperty.appTop @LocallyOfFiniteType _ inferInstance
  have hintegral : ((sectionsCocone D c i₀).comp ((p i₀).appTop.hom)).IsIntegral := by
    have heq : (sectionsCocone D c i₀).comp ((p i₀).appTop.hom) = f.appTop.hom := by
      refine RingHom.ext fun x ↦ ?_
      simp only [sectionsCocone, RingHom.comp_apply]
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← hf i₀]
    rw [heq]
    exact IsIntegralHom.isIntegral_app f ⊤ (isAffineOpen_top S)
  obtain ⟨j, hij, hj⟩ := Stacks.IntegralLimitAlgebra.exists_isIntegral
    (fun a b hab ↦ sectionsMap D a b hab) (finite_sectionsMap D hfinite)
    (fun a ↦ (p a).appTop.hom) hr
    (sectionsCocone_comp D c) (isSmallColimit_appTop D c hc) i₀ hftype hintegral
  refine ⟨j, hij, ?_⟩
  rw [IsFinite.iff_isIntegralHom_and_locallyOfFiniteType]
  exact ⟨isIntegralHom_of_isAffine (p j) inferInstance hj, inferInstance⟩

/-- The "for `i` large enough" form of `exists_isFinite_of_isAffine`.  The eventual half of the
conclusion is formal: the structure morphism at a later index is the transition morphism followed
by the structure morphism at an earlier one, and finiteness is stable under composition. -/
theorem eventually_isFinite_of_isAffine [IsDirectedOrder I] [Nonempty I]
    [∀ i, IsAffine (D.obj i)] {S : Scheme.{u}} [IsAffine S]
    (p : ∀ i : I, D.obj (op i) ⟶ S)
    (hp : ∀ (i j : I) (h : i ≤ j), p j = D.map (homOfLE h).op ≫ p i)
    (c : Cone D) (hc : IsLimit c) (f : c.pt ⟶ S) [IsIntegralHom f]
    (hf : ∀ i : I, f = c.π.app (op i) ≫ p i)
    (hfinite : ∀ (i j : I) (h : i ≤ j), IsFinite (D.map (homOfLE h).op))
    [∀ i : I, LocallyOfFiniteType (p i)] :
    ∀ᶠ j in Filter.atTop, IsFinite (p j) := by
  rw [Filter.eventually_atTop]
  obtain ⟨j, -, hj⟩ :=
    exists_isFinite_of_isAffine D p hp c hc f hf hfinite (Classical.arbitrary I)
  refine ⟨j, fun k hk ↦ ?_⟩
  have h₁ := hfinite j k hk
  have h₂ := hj
  rw [hp j k hk]
  infer_instance

end Stacks.IntegralLimitAffine

end

end
