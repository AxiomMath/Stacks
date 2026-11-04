module

public import StacksFrontier.AlgebraicGeometry.AffineReduction.Basic
public import StacksFrontier.AlgebraicGeometry.LimitIndexUniverseIntegral.Affine

/-!
# The full universal property of the small-colimit device, and sections of a limit

`Stacks.IntegralLimitAlgebra.IsSmallColimit` says, for a directed system of rings `A i` in
`Type u` indexed by a preorder `I` in an arbitrary universe and a cocone `ιL i : A i →+* L`
with `L : Type u`, that every compatible family of ring maps `A i →+* C` with `C : Type u`
factors through `L`: the existence half of a universal property. It holds for the global
sections of a limit of affine schemes (`Stacks.IntegralLimitAffine.isSmallColimit_appTop`) and
for the sections over the preimages of an affine open of a base
(`Stacks.Tag09ZNAffineReduction.isSmallColimit_limMap`).

This file defines the uniqueness half, `IsSmallColimitUnique`, proves it for both of those
cocones, and deduces that every element of `L` is `ιL i x` for some stage `i` and some
`x : A i`. For affine schemes this extends Mathlib's
`AlgebraicGeometry.exists_appTop_π_eq_of_isAffine_of_isLimit` to an index in an arbitrary
universe. All names are in the namespace `Stacks.SmallColimitUniversal`.

## Main definitions

* `IsSmallColimitUnique`: the uniqueness half of the universal property among rings in `Type u`.

## Main results

* `existsUnique_hom_of_isSmallColimit`: the two halves together, as an `∃!`.
* `exists_eq_of_isSmallColimit`: **every element of `L` comes from a stage**, from the two halves
  and directedness of the index.
* `isSmallColimitUnique_appTop`, `exists_appTop_eq_of_isAffine`: the uniqueness half and the
  descent of a section for the global sections of a limit of affine schemes with affine vertex.
* `isSmallColimitUnique_limMap`, `exists_app_eq_of_isAffineOpen`: the same over the preimages of
  an open of a base whose preimages at the stages and in the vertex are affine.

## References

* [The Stacks Project, Tag 01Z6](https://stacks.math.columbia.edu/tag/01Z6)
* [The Stacks Project, Tag 09ZN](https://stacks.math.columbia.edu/tag/09ZN)
-/

@[expose] public section

noncomputable section

universe w u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Stacks.SmallColimitUniversal

/-! ### The uniqueness half of the universal property -/

variable {I : Type w} [Preorder I] {A : I → Type u} [∀ i, CommRing (A i)]
  (ψ : ∀ i j, i ≤ j → A i →+* A j)

/-- `IsSmallColimitUnique ιL` is the *uniqueness* half of the universal property of the cocone
`ιL` among commutative rings in `Type u`: two ring maps out of `L` agreeing on the image of every
stage are equal. -/
def IsSmallColimitUnique {L : Type u} [CommRing L] (ιL : ∀ i, A i →+* L) : Prop :=
  ∀ (C : Type u) [CommRing C] (G₁ G₂ : L →+* C),
    (∀ (i : I) (x : A i), G₁ (ιL i x) = G₂ (ιL i x)) → G₁ = G₂

/-- **The full universal property of the cocone among rings in `Type u`.**  A compatible family of
ring maps out of the stages into a ring in the stages' own universe factors through `L` through a
*unique* ring map, whatever universe the index lives in. -/
theorem existsUnique_hom_of_isSmallColimit {L : Type u} [CommRing L] {ιL : ∀ i, A i →+* L}
    (huniv : Stacks.IntegralLimitAlgebra.IsSmallColimit ψ ιL)
    (huniq : IsSmallColimitUnique ιL) (C : Type u) [CommRing C] (g : ∀ i, A i →+* C)
    (hg : ∀ i j (h : i ≤ j) (x : A i), g j (ψ i j h x) = g i x) :
    ∃! G : L →+* C, ∀ i x, G (ιL i x) = g i x := by
  obtain ⟨G, hG⟩ := huniv C g hg
  exact ⟨G, hG, fun G' hG' ↦ huniq C G' G fun i x ↦ (hG' i x).trans (hG i x).symm⟩

/-- **Every element of the vertex of a cocone with the full universal property comes from a
stage**, for a nonempty directed index in an arbitrary universe. -/
theorem exists_eq_of_isSmallColimit [IsDirectedOrder I] [Nonempty I] {L : Type u} [CommRing L]
    {ιL : ∀ i, A i →+* L} (hιL : ∀ i j (h : i ≤ j) (x : A i), ιL j (ψ i j h x) = ιL i x)
    (huniv : Stacks.IntegralLimitAlgebra.IsSmallColimit ψ ιL)
    (huniq : IsSmallColimitUnique ιL) (z : L) :
    ∃ (i : I) (x : A i), ιL i x = z := by
  have hmono : ∀ i j, i ≤ j → (ιL i).range ≤ (ιL j).range := fun i j h y hy ↦ by
    obtain ⟨x, rfl⟩ := RingHom.mem_range.mp hy
    exact RingHom.mem_range.mpr ⟨ψ i j h x, hιL i j h x⟩
  have hdir : Directed (· ≤ ·) fun i ↦ (ιL i).range := fun i j ↦ by
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    exact ⟨k, hmono i k hik, hmono j k hjk⟩
  obtain ⟨G, hG⟩ := huniv ↥(⨆ i, (ιL i).range)
    (fun i ↦ (ιL i).codRestrict (⨆ i, (ιL i).range) fun x ↦
      le_iSup (fun i ↦ (ιL i).range) i ((ιL i).mem_range_self x))
    fun i j h x ↦ Subtype.ext (hιL i j h x)
  have hid : (⨆ i, (ιL i).range).subtype.comp G = RingHom.id L :=
    huniq L _ _ fun i x ↦ congrArg (fun y : ↥(⨆ i, (ιL i).range) ↦ (y : L)) (hG i x)
  have h : (G z : L) = z := by simpa using congrArg (fun φ : L →+* L ↦ φ z) hid
  have hz : z ∈ ⨆ i, (ιL i).range := h ▸ (G z).2
  obtain ⟨i, hi⟩ := (Subring.mem_iSup_of_directed hdir).mp hz
  exact ⟨i, RingHom.mem_range.mp hi⟩

/-- Ring maps out of `R` are equal if their `Spec`s agree after composing with a monomorphism. -/
private theorem ringHom_ext_of_spec_map_comp_eq {R : CommRingCat.{u}} {C : Type u} [CommRing C]
    {X : Scheme.{u}} (e : Spec R ⟶ X) [Mono e] {G₁ G₂ : ↥R →+* C}
    (hm : Spec.map (CommRingCat.ofHom G₁) ≫ e = Spec.map (CommRingCat.ofHom G₂) ≫ e) :
    G₁ = G₂ := by
  simpa using congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).mp hm))

/-! ### Global sections of a limit of affine schemes -/

section AppTop

open Stacks.IntegralLimitAffine

variable {I : Type w} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u})

/-- **The uniqueness half for the global sections of a limit of affine schemes with affine
vertex**, at an index in an arbitrary universe. -/
theorem isSmallColimitUnique_appTop [∀ i, IsAffine (D.obj i)] (c : Cone D) (hc : IsLimit c)
    [IsAffine c.pt] :
    IsSmallColimitUnique (sectionsCocone D c) := by
  intro C _ G₁ G₂ h
  have key : ∀ (G : ↥Γ(c.pt, ⊤) →+* C) {Y : Scheme.{u}} [IsAffine Y] (q : c.pt ⟶ Y),
      Spec.map (CommRingCat.ofHom G) ≫ c.pt.isoSpec.inv ≫ q
        = Spec.map (q.appTop ≫ CommRingCat.ofHom G) ≫ Y.isoSpec.inv := by
    intro G Y _ q
    rw [Spec.map_comp, Category.assoc, Scheme.isoSpec_inv_naturality]
  have hm : Spec.map (CommRingCat.ofHom G₁) ≫ c.pt.isoSpec.inv
      = Spec.map (CommRingCat.ofHom G₂) ≫ c.pt.isoSpec.inv := by
    refine hc.hom_ext fun W ↦ ?_
    have hAB : (c.π.app W).appTop ≫ CommRingCat.ofHom G₁
        = (c.π.app W).appTop ≫ CommRingCat.ofHom G₂ :=
      CommRingCat.hom_ext (RingHom.ext fun x ↦ h W.unop x)
    rw [Category.assoc, Category.assoc, key G₁ (c.π.app W), key G₂ (c.π.app W), hAB]
  exact ringHom_ext_of_spec_map_comp_eq _ hm

/-- The full universal property of the cocone on global sections, for a limit of affine schemes
with affine vertex, at a free index universe. -/
theorem existsUnique_hom_appTop [∀ i, IsAffine (D.obj i)] (c : Cone D) (hc : IsLimit c)
    [IsAffine c.pt] (C : Type u) [CommRing C] (g : ∀ i : I, ↥Γ(D.obj (op i), ⊤) →+* C)
    (hg : ∀ (i j : I) (h : i ≤ j) (x : ↥Γ(D.obj (op i), ⊤)),
      g j (sectionsMap D i j h x) = g i x) :
    ∃! G : ↥Γ(c.pt, ⊤) →+* C, ∀ i x, G (sectionsCocone D c i x) = g i x :=
  existsUnique_hom_of_isSmallColimit _ (isSmallColimit_appTop D c hc)
    (isSmallColimitUnique_appTop D c hc) C g hg

/-- **Every global section of the vertex of a limit of affine schemes comes from a stage, at an
index universe independent of the scheme universe.** This is
`AlgebraicGeometry.exists_appTop_π_eq_of_isAffine_of_isLimit` at an index in an arbitrary
universe. -/
theorem exists_appTop_eq_of_isAffine [IsDirectedOrder I] [Nonempty I] [∀ i, IsAffine (D.obj i)]
    (c : Cone D) (hc : IsLimit c) [IsAffine c.pt] (z : ↥Γ(c.pt, ⊤)) :
    ∃ (i : I) (x : ↥Γ(D.obj (op i), ⊤)), (c.π.app (op i)).appTop.hom x = z :=
  exists_eq_of_isSmallColimit (fun i j h ↦ sectionsMap D i j h) (sectionsCocone_comp D c)
    (isSmallColimit_appTop D c hc) (isSmallColimitUnique_appTop D c hc) z

end AppTop

/-! ### Sections over the preimages of an open of a base -/

section LimMap

open Stacks.Tag09ZNAffineReduction

variable {I : Type w} [Preorder I] {S : Scheme.{u}} {D : Iᵒᵖ ⥤ Scheme.{u}}
  {p : ∀ i : I, D.obj (op i) ⟶ S} {c : Cone D} {f : c.pt ⟶ S}

/-- **The uniqueness half for the sections over the preimages of an open of the base**, when
those preimages are affine at every stage and in the vertex, at an index in an arbitrary
universe. -/
theorem isSmallColimitUnique_limMap (hc : IsLimit c)
    (hf : ∀ i : I, f = c.π.app (op i) ≫ p i) (V : S.Opens)
    (haff : ∀ i : I, IsAffineOpen (p i ⁻¹ᵁ V)) (hW : IsAffineOpen (f ⁻¹ᵁ V)) :
    IsSmallColimitUnique (limMap hf V) := by
  intro C _ G₁ G₂ h
  have key : ∀ (G : ↥Γ(c.pt, f ⁻¹ᵁ V) →+* C) (i : I),
      Spec.map (CommRingCat.ofHom G) ≫ hW.fromSpec ≫ c.π.app (op i)
        = Spec.map (((c.π.app (op i)).appLE (p i ⁻¹ᵁ V) (f ⁻¹ᵁ V) (limPreimage_eq hf V i).le)
            ≫ CommRingCat.ofHom G) ≫ (haff i).fromSpec := by
    intro G i
    rw [Spec.map_comp, Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec
      (c.π.app (op i)) (haff i) hW (limPreimage_eq hf V i).le]
  have hm : Spec.map (CommRingCat.ofHom G₁) ≫ hW.fromSpec
      = Spec.map (CommRingCat.ofHom G₂) ≫ hW.fromSpec := by
    refine hc.hom_ext fun W ↦ ?_
    obtain ⟨i⟩ := W
    have hAB : ((c.π.app (op i)).appLE (p i ⁻¹ᵁ V) (f ⁻¹ᵁ V) (limPreimage_eq hf V i).le)
          ≫ CommRingCat.ofHom G₁
        = ((c.π.app (op i)).appLE (p i ⁻¹ᵁ V) (f ⁻¹ᵁ V) (limPreimage_eq hf V i).le)
          ≫ CommRingCat.ofHom G₂ :=
      CommRingCat.hom_ext (RingHom.ext fun x ↦ h i x)
    rw [Category.assoc, Category.assoc, key G₁ i, key G₂ i, hAB]
  exact ringHom_ext_of_spec_map_comp_eq _ hm

/-- The full universal property of the cocone of sections over the preimages of an open of the
base, at a free index universe. -/
theorem existsUnique_hom_limMap (hp : IsStructureFamily D p) (hc : IsLimit c)
    (hf : ∀ i : I, f = c.π.app (op i) ≫ p i) (V : S.Opens)
    (haff : ∀ i : I, IsAffineOpen (p i ⁻¹ᵁ V)) (hW : IsAffineOpen (f ⁻¹ᵁ V)) [Nonempty I]
    (C : Type u) [CommRing C] (g : ∀ i : I, ↥Γ(D.obj (op i), p i ⁻¹ᵁ V) →+* C)
    (hg : ∀ (i j : I) (h : i ≤ j) (x : ↥Γ(D.obj (op i), p i ⁻¹ᵁ V)),
      g j (transMap hp V i j h x) = g i x) :
    ∃! G : ↥Γ(c.pt, f ⁻¹ᵁ V) →+* C, ∀ i x, G (limMap hf V i x) = g i x :=
  existsUnique_hom_of_isSmallColimit _ (isSmallColimit_limMap hp hc hf V haff hW)
    (isSmallColimitUnique_limMap hc hf V haff hW) C g hg

/-- **Every section of the limit over the preimage of an open of the base comes from a stage, at
an index universe independent of the scheme universe**, when the preimage of `V` is affine at
every stage and in the vertex of the limit cone (the stages themselves need not be affine; this
is the setting of the reduction of [Stacks, Tag 09ZN] to [Stacks, Tag 09ZM]). -/
theorem exists_app_eq_of_isAffineOpen [IsDirectedOrder I] [Nonempty I]
    (hp : IsStructureFamily D p) (hc : IsLimit c)
    (hf : ∀ i : I, f = c.π.app (op i) ≫ p i) (V : S.Opens)
    (haff : ∀ i : I, IsAffineOpen (p i ⁻¹ᵁ V)) (hW : IsAffineOpen (f ⁻¹ᵁ V))
    (z : ↥Γ(c.pt, f ⁻¹ᵁ V)) :
    ∃ (i : I) (x : ↥Γ(D.obj (op i), p i ⁻¹ᵁ V)), limMap hf V i x = z :=
  exists_eq_of_isSmallColimit (fun i j h ↦ transMap hp V i j h) (limMap_transMap hp hf V)
    (isSmallColimit_limMap hp hc hf V haff hW) (isSmallColimitUnique_limMap hc hf V haff hW) z

end LimMap

end Stacks.SmallColimitUniversal

end

end
