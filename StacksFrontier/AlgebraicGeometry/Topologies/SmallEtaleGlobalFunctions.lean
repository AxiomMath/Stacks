module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.Coverage
public import Mathlib.CategoryTheory.Sites.CoverPreserving
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The presheaf of global functions is a sheaf for the fpqc topology

The presheaf of rings `T ↦ Γ(T, 𝒪_T)` on the category of all schemes is a sheaf for the fpqc
topology, hence for every coarser topology.  This is descent of functions, the case of the
structure sheaf of faithfully flat descent for quasi-coherent modules.

The proof is representability: `Γ(T, 𝒪_T)` is the set of `T`-points of the affine line over
`Spec ℤ`, and the fpqc topology is subcanonical.  What this leaves is the passage from the
underlying presheaf of types to the presheaf of rings, which is carried out by
`Stacks.Sites.isSheaf_ringCat_of_isSheaf_forget`: a presheaf of rings whose underlying presheaf
of types is a sheaf is a sheaf, with no universe restriction on the site.  (Mathlib's
`CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget` does not apply, because it needs the
morphisms of the target category to live in the universe `max u v` of the site, which fails for
`RingCat.{u}` over `Scheme.{u}`.)

This file also records two general tools about transporting the sheaf condition along a functor
`G : C ⥤ D`, used to pass from the big site of all schemes to a small site.  Mathlib's
`CategoryTheory.Functor.isContinuous_of_coverPreserving` is not usable here, because it needs the
cover-preservation statement for *every* covering sieve of the generated topology, whereas the
covering sieves of a small site are only described through the covering families generating it.

## Main definitions

* `Stacks.Sites.affineLineOverInt` is `Spec ℤ[t]`, the affine line over `Spec ℤ`.
* `Stacks.Sites.globalSectionsSheaf` is the sheaf of types `T ↦ Γ(T, 𝒪_T)` on the fpqc site.

## Main results

* `Stacks.Sites.isSheaf_ringCat_of_isSheaf_forget`: a presheaf of rings is a sheaf as soon as its
  underlying presheaf of types is.
* `Stacks.Sites.compatiblePreserving_of_lift`: a functor along which cospans of the source
  category can be completed is compatible-preserving.
* `Stacks.Sites.isSheafFor_op_comp`: a compatible-preserving functor transports the sheaf
  condition for a single sieve.
* `Stacks.Sites.isSheaf_fpqcTopology_globalSections` and
  `Stacks.Sites.isSheaf_fpqcTopology_structurePresheaf`: the presheaf of global functions is an
  fpqc sheaf of types, respectively of rings.

## References

* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T), of which the results
  here are the structure-sheaf case
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite

universe w v₁ v₂ u₁ u₂ u

namespace Stacks.Sites

section Concrete

variable {C : Type u₁} [Category.{v₁} C]

/-- A presheaf of rings whose underlying presheaf of types is a sheaf is a sheaf.  The
amalgamation of a compatible family of ring homomorphisms is computed element by element in the
underlying types, and it is a ring homomorphism because the restriction maps are jointly
injective on a covering sieve. -/
@[ega "0 3.1.4" "more general"]
public theorem isSheaf_ringCat_of_isSheaf_forget (J : GrothendieckTopology C)
    (P : Cᵒᵖ ⥤ RingCat.{w})
    (h : Presieve.IsSheaf J (P ⋙ CategoryTheory.forget RingCat)) :
    Presheaf.IsSheaf J P := by
  classical
  intro E X S hS x hx
  let y : ∀ ⦃Y : C⦄ (f : Y ⟶ X), S f → (E ⟶ P.obj (op Y)) := fun _ f hf => x f hf
  have hy : ∀ ⦃Y₁ Y₂ Z : C⦄ (g₁ : Z ⟶ Y₁) (g₂ : Z ⟶ Y₂) {f₁ : Y₁ ⟶ X} {f₂ : Y₂ ⟶ X}
      (h₁ : S f₁) (h₂ : S f₂), g₁ ≫ f₁ = g₂ ≫ f₂ →
      y f₁ h₁ ≫ P.map g₁.op = y f₂ h₂ ≫ P.map g₂.op :=
    fun _ _ _ g₁ g₂ _ _ h₁ h₂ hcomm => hx g₁ g₂ h₁ h₂ hcomm
  have key : ∀ e : ToType E, ∃! t : ToType (P.obj (op X)),
      ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄ (hf : S f), P.map f.op t = y f hf e := by
    intro e
    refine h S hS (fun _ f hf => y f hf e) ?_
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hcomm
    exact ConcreteCategory.congr_hom (hy g₁ g₂ h₁ h₂ hcomm) e
  have hsep := (h S hS).isSeparatedFor
  have hext : ∀ t₁ t₂ : ToType (P.obj (op X)),
      (∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄ (_ : S f), P.map f.op t₁ = P.map f.op t₂) → t₁ = t₂ :=
    fun _ _ h => hsep.ext fun _ _ hf => h hf
  have hc := fun e => (key e).exists.choose_spec
  refine ⟨RingCat.ofHom
    { toFun := fun e => (key e).exists.choose
      map_one' := ?_
      map_mul' := ?_
      map_zero' := ?_
      map_add' := ?_ }, ?_, ?_⟩
  · exact hext _ _ fun _ _ hf => by rw [hc 1 hf]; simp
  · exact fun a b => hext _ _ fun _ _ hf => by
      rw [hc (a * b) hf, map_mul, map_mul, hc a hf, hc b hf]
  · exact hext _ _ fun _ _ hf => by rw [hc 0 hf]; simp
  · exact fun a b => hext _ _ fun _ _ hf => by
      rw [hc (a + b) hf, map_add, map_add, hc a hf, hc b hf]
  · exact fun Y f hf => ConcreteCategory.hom_ext _ _ fun e => (key e).exists.choose_spec hf
  · exact fun t ht => ConcreteCategory.hom_ext _ _ fun e =>
      (key e).unique (fun _ f hf => ConcreteCategory.congr_hom (ht f hf) e)
        (key e).exists.choose_spec

end Concrete

section Transport

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- A functor `G : C ⥤ D` is compatible-preserving as soon as every cospan in `C` with an apex
in `D` over it can be completed inside `C`: this is the only consequence of representable
flatness that `CategoryTheory.CompatiblePreserving` uses, and unlike flatness it does not ask
the comma categories to be nonempty. -/
public theorem compatiblePreserving_of_lift (K : GrothendieckTopology D) (G : C ⥤ D)
    (hlift : ∀ ⦃Y₁ Y₂ Z : C⦄ (g₁ : Y₁ ⟶ Z) (g₂ : Y₂ ⟶ Z) ⦃X : D⦄
      (f₁ : X ⟶ G.obj Y₁) (f₂ : X ⟶ G.obj Y₂), f₁ ≫ G.map g₁ = f₂ ≫ G.map g₂ →
      ∃ (W : C) (π₁ : W ⟶ Y₁) (π₂ : W ⟶ Y₂) (k : X ⟶ G.obj W),
        π₁ ≫ g₁ = π₂ ≫ g₂ ∧ k ≫ G.map π₁ = f₁ ∧ k ≫ G.map π₂ = f₂) :
    CompatiblePreserving.{w} K G := by
  constructor
  intro ℱ Z T x hx Y₁ Y₂ X f₁ f₂ g₁ g₂ hg₁ hg₂ e
  obtain ⟨W, π₁, π₂, k, hcomm, h₁, h₂⟩ := hlift g₁ g₂ f₁ f₂ e
  rw [← h₁, ← h₂]
  simp only [op_comp, ℱ.obj.map_comp, types_comp_apply]
  exact congrArg _ (hx π₁ π₂ hg₁ hg₂ hcomm)

/-- Restricting a sheaf along a compatible-preserving functor satisfies the sheaf condition for
every sieve whose image generates a covering sieve.  This is the single-sieve content of
`CategoryTheory.Functor.isContinuous_of_coverPreserving`, which demands instead that *all*
covering sieves of a topology on `C` have covering images. -/
public theorem isSheafFor_op_comp {G : C ⥤ D} {K : GrothendieckTopology D}
    (hG : CompatiblePreserving.{w} K G) (ℱ : Sheaf K (Type w)) {X : C} (S : Sieve X)
    (hS : S.functorPushforward G ∈ K (G.obj X)) :
    Presieve.IsSheafFor (G.op ⋙ ℱ.obj) S.arrows := by
  intro x hx
  apply existsUnique_of_exists_of_unique
  · have H := (isSheaf_iff_isSheaf_of_type _ _).1 ℱ.2 _ hS
    exact ⟨H.amalgamate (x.functorPushforward G) (hx.functorPushforward hG),
      fun V f hf => (H.isAmalgamation (hx.functorPushforward hG) (G.map f) _).trans
        (hG.apply_map _ hx hf)⟩
  · intro y₁ y₂ hy₁ hy₂
    apply (((isSheaf_iff_isSheaf_of_type _ _).1 ℱ.2).isSeparated _ hS).ext
    rintro Y _ ⟨Z, g, h, hg, rfl⟩
    simpa using! congrArg _ ((hy₁ g hg).trans (hy₂ g hg).symm)

end Transport

section GlobalFunctions

/-- The affine line over `Spec ℤ`, the scheme whose points with values in `T` are the global
functions on `T`. -/
@[ega "I 3.3.15" "partial"]
public noncomputable def affineLineOverInt : Scheme.{u} :=
  Spec (CommRingCat.of (MvPolynomial PUnit.{u + 1} (ULift.{u} ℤ)))

/-- The presheaf of types of global functions is represented by the affine line. -/
@[ega "I 3.3.15" "partial", ega "II 1.7.13" "special case", sga "3 I 4.3.1" "partial"]
public noncomputable def globalSectionsIsoYoneda :
    Scheme.Γ.{u} ⋙ CategoryTheory.forget CommRingCat ≅ yoneda.obj affineLineOverInt.{u} :=
  (NatIso.ofComponents (fun T => Equiv.toIso
    ((AffineSpace.toSpecMvPolyIntEquiv (X := T.unop) PUnit.{u + 1}).trans
      (Equiv.funUnique _ _))) (fun _ => rfl)).symm

/-- **Étale descent of functions**, the presheaf of types.  Global functions form a sheaf of
types for the fpqc topology on the category of all schemes, because they are the points of the
affine line and the fpqc topology is subcanonical. -/
public theorem isSheaf_fpqcTopology_globalSections :
    Presieve.IsSheaf Scheme.fpqcTopology.{u}
      (Scheme.Γ.{u} ⋙ CategoryTheory.forget CommRingCat) := by
  rw [← isSheaf_iff_isSheaf_of_type, Presheaf.isSheaf_of_iso_iff globalSectionsIsoYoneda,
    isSheaf_iff_isSheaf_of_type]
  exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _

/-- Global functions as a sheaf of types on the fpqc site of all schemes. -/
public noncomputable def globalSectionsSheaf : Sheaf Scheme.fpqcTopology.{u} (Type u) :=
  ⟨Scheme.Γ.{u} ⋙ CategoryTheory.forget CommRingCat,
    (isSheaf_iff_isSheaf_of_type _ _).2 isSheaf_fpqcTopology_globalSections⟩

/-- The underlying presheaf of `Stacks.Sites.globalSectionsSheaf` is the presheaf of global
functions. -/
@[simp]
public theorem globalSectionsSheaf_obj :
    globalSectionsSheaf.{u}.obj = Scheme.Γ.{u} ⋙ CategoryTheory.forget CommRingCat := rfl

/-- **Étale descent of functions**, the presheaf of rings.  The structure presheaf
`T ↦ Γ(T, 𝒪_T)` of the category of all schemes is a sheaf of rings for the fpqc topology. -/
public theorem isSheaf_fpqcTopology_structurePresheaf :
    Presheaf.IsSheaf Scheme.fpqcTopology.{u}
      (Scheme.Γ.{u} ⋙ forget₂ CommRingCat RingCat) :=
  isSheaf_ringCat_of_isSheaf_forget _ _ isSheaf_fpqcTopology_globalSections

/-- The étale topology is coarser than the fpqc topology. -/
@[stacks 03O4 "étale topology", sga "4 VII 4.2" "étale ≤ fpqc", sga "3 IV 6.6" "(6.6.1) ét ≤ fpqc"]
public theorem etaleTopology_le_fpqcTopology :
    Scheme.etaleTopology.{u} ≤ Scheme.fpqcTopology.{u} :=
  Scheme.etaleTopology_le_proetaleTopology.trans Scheme.proetaleTopology_le_fpqcTopology

end GlobalFunctions

end Stacks.Sites

end
