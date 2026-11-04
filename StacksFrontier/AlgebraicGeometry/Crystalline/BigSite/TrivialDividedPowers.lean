module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import StacksFrontier.AlgebraicGeometry.Crystalline.Scheme
public import StacksFrontier.AlgebraicGeometry.HigherDirectImage.Basic
public import StacksFrontier.CategoryTheory.Sites.Modules.IdealSubsheaf

/-!
# The trivial divided power structure on a scheme

Every scheme `X` carries a divided power structure in a trivial way: take the zero ideal sheaf,
which has a unique divided power structure.  The resulting divided power scheme is the one used to
regard an ordinary scheme as an object of a crystalline category, where it plays the role of the
divided power thickening `(U, U, ∅)` of `U` by itself.

Making this precise needs two facts about the zero submodule of a sheaf of modules that are not in
Mathlib: that the bottom element of the lattice of subsheaves has all of its ideals of sections
equal to `⊥` (`SheafOfModules.Submodule.bot_obj`, from the separatedness of the ambient sheaf), and
that a zero sheaf of modules is quasi-coherent, which is
`Stacks.AlgebraicGeometry.HigherDirectImage.isQuasicoherent_of_isZero` (via the free sheaf on an
empty index type, which is locally free).  Together they give
`Crystalline.isQuasicoherent_bot_toSheafOfModules`, the quasi-coherence of the zero ideal sheaf of
a scheme.

The divided power compatibility that the trivial structure needs is always the same statement: a
ring homomorphism into a ring whose divided power ideal is zero is a divided power morphism as
soon as it kills the source ideal (`DividedPowers.IsDPMorphism.of_eq_bot`).  Only the divided
power axioms `dpow_zero` and `dpow_mem` are used, never the formula for
`DividedPowers.dividedPowersBot`.

## Main definitions

* `DividedPowers.ofEqBot` — the divided power structure on an ideal known to be zero.
* `Crystalline.trivialDividedPowerScheme` — a scheme with its zero divided power ideal.

## Main results

* `SheafOfModules.Submodule.bot_obj` — the zero subsheaf has zero ideal of sections over every
  object of the site.
* `DividedPowers.IsDPMorphism.of_eq_bot` — a ring map killing the source divided power ideal is a
  divided power morphism into a ring with zero divided power ideal.
* `AlgebraicGeometry.Scheme.Hom.app_eq_zero_of_mem_of_le_ker` — a morphism of schemes whose kernel
  ideal sheaf contains a subsheaf of `𝒪_X` on affine opens kills that subsheaf over every open.

## References

* [Stacks Project, Tag 07I3](https://stacks.math.columbia.edu/tag/07I3)
* [Stacks Project, Tag 07I8](https://stacks.math.columbia.edu/tag/07I8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v v₁ u₁ u

namespace SheafOfModules

section Free

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The free sheaf of modules on an empty index type is a zero object: morphisms out of it are
families of sections indexed by the empty type, so its identity is its zero endomorphism. -/
theorem isZero_free_of_isEmpty (I : Type u) [IsEmpty I] : IsZero (free (R := R) I) := by
  rw [IsZero.iff_id_eq_zero]
  exact (free (R := R) I).freeHomEquiv.injective (funext fun i ↦ (IsEmpty.false i).elim)

end Free

section Quasicoherent

variable {C : Type u₁} [Category.{v₁} C] [HasBinaryProducts C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- A zero sheaf of modules is quasi-coherent: it is isomorphic to the free sheaf on the empty
index type, which is locally free. This is
`Stacks.AlgebraicGeometry.HigherDirectImage.isQuasicoherent_of_isZero` under the name the
crystalline development uses. -/
theorem IsQuasicoherent.of_isZero {M : SheafOfModules.{u} R} (hM : IsZero M) :
    M.IsQuasicoherent :=
  Stacks.AlgebraicGeometry.HigherDirectImage.isQuasicoherent_of_isZero hM

end Quasicoherent

end SheafOfModules

namespace AlgebraicGeometry

open AlgebraicGeometry
open scoped AlgebraicGeometry

/-- **A morphism of schemes kills, over every open, a subsheaf of the structure sheaf that its
kernel ideal sheaf contains over every affine open.**  The affine opens contained in the given
open cover it, the subsheaf is stable under restriction, and over an affine open the kernel ideal
sheaf is contained in the kernel of the map on sections; the conclusion then follows from the
sheaf axiom on the source. -/
theorem Scheme.Hom.app_eq_zero_of_mem_of_le_ker {X Y : Scheme.{u}} (i : Y ⟶ X)
    (N : (SheafOfModules.unit X.ringCatSheaf).Submodule)
    (hN : ∀ U : X.affineOpens, N.obj (op U.1) ≤ i.ker.ideal U)
    (V : X.Opens) (s : Γ(X, V)) (hs : s ∈ N.obj (op V)) : i.app V s = 0 := by
  choose W hW hxW hWV using fun x : V ↦
    Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (U := V) (x := x.1) x.2
  refine TopCat.Sheaf.eq_of_locally_eq' Y.sheaf (fun x : V ↦ i ⁻¹ᵁ W x) (i ⁻¹ᵁ V)
    (fun x ↦ (Opens.map i.base).map (homOfLE (hWV x))) (fun z hz ↦ ?_) (i.app V s) 0 fun x ↦ ?_
  · exact Opens.mem_iSup.2 ⟨⟨i.base z, hz⟩, hxW ⟨i.base z, hz⟩⟩
  · have hnat := ConcreteCategory.congr_hom (i.naturality (homOfLE (hWV x)).op) s
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at hnat
    have hvan : i.app (W x) (X.presheaf.map (homOfLE (hWV x)).op s) = 0 :=
      i.ideal_ker_le ⟨W x, hW x⟩ (hN ⟨W x, hW x⟩ (N.map_mem (homOfLE (hWV x)).op hs))
    exact (hnat.symm.trans hvan).trans (map_zero _).symm

end AlgebraicGeometry

namespace DividedPowers

/-- The divided power structure on an ideal that is known to be zero. -/
noncomputable def ofEqBot {A : Type*} [CommSemiring A] {I : Ideal A} (h : I = ⊥) :
    DividedPowers I := by
  subst h
  exact dividedPowersBot A

/-- **A ring homomorphism killing the source divided power ideal is a divided power morphism into
any ring whose divided power ideal is zero.**  Only the axioms `dpow_zero` and `dpow_mem` are
used: in degree `0` both sides are `1`, and in positive degree both sides lie in an ideal that is
zero. -/
theorem IsDPMorphism.of_eq_bot {A B : Type*} [CommSemiring A] [CommSemiring B] {I : Ideal A}
    {K : Ideal B} (hI : DividedPowers I) (hK : DividedPowers K) (f : A →+* B) (hK0 : K = ⊥)
    (hf : I.map f ≤ K) : IsDPMorphism hI hK f where
  ideal_comp := hf
  dpow_comp {n} a ha := by
    have hfa : f a ∈ K := hf (Ideal.mem_map_of_mem f ha)
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      rw [hK.dpow_zero hfa, hI.dpow_zero ha, map_one]
    · have hbot := Submodule.eq_bot_iff _ |>.mp hK0
      rw [hbot _ (hK.dpow_mem hn.ne' hfa),
        hbot _ (hf (Ideal.mem_map_of_mem f (hI.dpow_mem hn.ne' ha)))]

end DividedPowers

namespace Crystalline

open AlgebraicGeometry
open scoped AlgebraicGeometry

/-- The zero ideal sheaf of a scheme is quasi-coherent, being a zero object. -/
theorem isQuasicoherent_bot_toSheafOfModules (X : Scheme.{u}) :
    ((⊥ : (SheafOfModules.unit X.ringCatSheaf).Submodule).toSheafOfModules).IsQuasicoherent := by
  refine Stacks.AlgebraicGeometry.HigherDirectImage.isQuasicoherent_of_isZero
    (M := (⊥ : (SheafOfModules.unit X.ringCatSheaf).Submodule).toSheafOfModules) ?_
  rw [IsZero.iff_id_eq_zero]
  ext U x
  have h : ((⊥ : (SheafOfModules.unit X.ringCatSheaf).Submodule).obj U) = ⊥ :=
    SheafOfModules.Submodule.bot_obj _ _
  exact (h ▸ inferInstance : Subsingleton
    ↥((⊥ : (SheafOfModules.unit X.ringCatSheaf).Submodule).obj U)).elim _ _

/-- **A scheme as a divided power scheme with zero divided power ideal.**  The zero ideal sheaf is
quasi-coherent and carries a unique divided power structure; this is the divided power scheme
underlying the trivial divided power thickening `(U, U, ∅)` of [Stacks, Tag 07I8]. -/
noncomputable def trivialDividedPowerScheme (X : Scheme.{u}) : DividedPowerScheme.{u} where
  scheme := X
  ideal := ⊥
  isQuasicoherent := isQuasicoherent_bot_toSheafOfModules X
  dividedPowers :=
    { dividedPowers U := DividedPowers.ofEqBot (SheafOfModules.Submodule.bot_obj _ U)
      naturality f := DividedPowers.IsDPMorphism.of_eq_bot _ _ _
        (SheafOfModules.Submodule.bot_obj _ _) (by
          simp only [sectionIdeal, SheafOfModules.Submodule.bot_obj]
          exact Ideal.map_le_iff_le_comap.mpr bot_le) }

/-- The underlying scheme of `trivialDividedPowerScheme X` is `X`. -/
@[simp]
lemma trivialDividedPowerScheme_scheme (X : Scheme.{u}) :
    (trivialDividedPowerScheme X).scheme = X := rfl

/-- The divided power ideal of `trivialDividedPowerScheme X` is the zero ideal sheaf. -/
@[simp]
lemma trivialDividedPowerScheme_ideal (X : Scheme.{u}) :
    (trivialDividedPowerScheme X).ideal = ⊥ := rfl

end Crystalline

end
