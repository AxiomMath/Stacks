module

public import Mathlib.Algebra.Homology.Refinements
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.CategoryTheory.Abelian.Exact
public import StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.Defs
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Ring.RingNF
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import StacksCore.CategoryTheory.Abelian.Subobject
public import StacksCore.CategoryTheory.Subobject.Lattice
public import StacksFrontier.Algebra.Homology.SpectralSequence.Boundedness
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Cycles
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Basic.InducedFiltration
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Basic.PageComplex
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Basic.StablePage

/-!
# Spectral sequences of filtered complexes: comparison and convergence

The comparison `E_∞^{p, q} ≅ gr^p H^n(K^•)` and the subquotient of [Stacks, Tag 012Q] as data,
and the convergence theorems [Stacks, Tag 012W], [Stacks, Tag 0BK5] and [Stacks, Tag 012M].
-/

@[expose] public section

universe v u

open CategoryTheory Limits Preadditive Opposite

namespace CochainComplex

section StableComparison

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : FilteredObject (CochainComplex C ℤ) ℤᵒᵖ) (p n : ℤ)
  (F : ℤ → ∀ m : ℤ, Subobject (K.X.X m)) (A : Subobject (K.X.cycles n))
  (Z B : Subobject (K.X.X n))

/-! #### The comparison `E_∞^{p, q} ≅ gr^pH^n(K^•)` of [Stacks, Tag 012V], as data -/

/-- **The comparison of [Stacks, Tag 012V] exists once (012S) and (012T) are equalities.** The
forward direction of
`CochainComplex.exists_iso_stablePage_iff_and_isGLB_isLUB_inducedFiltration_iff`, with the
subobjects `N` and `D` of that statement spelled out and the biconditional discharged. -/
public lemma exists_iso_stablePage_of_eq_sup
    (hF : ∀ p' m : ℤ, F p' m = Subobject.mk ((K.filtration.ι.app (op p')).f m))
    (hA : A = (Subobject.pullback (K.X.iCycles n)).obj (F p n))
    (hZ : IsGLB (Set.range fun r : ℕ =>
      F p n ⊓ (Subobject.pullback (K.X.d n (n + 1))).obj (F (p + r) (n + 1)) ⊔ F (p + 1) n) Z)
    (hB : IsLUB (Set.range fun r : ℕ =>
      F p n ⊓ (Subobject.«exists» (K.X.d (n - 1) n)).obj (F (p - r) (n - 1)) ⊔ F (p + 1) n) B)
    (hZN : Z = kernelSubobject (K.X.d n (n + 1)) ⊓ F p n ⊔ F (p + 1) n)
    (hBD : B = imageSubobject (K.X.d (n - 1) n) ⊓ F p n ⊔ F (p + 1) n)
    (a : (A : C) ⟶ (Z : C)) (ha : a ≫ Z.arrow = A.arrow ≫ K.X.iCycles n)
    (b : (A : C) ⟶ image (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n))
    (hb : b ≫ image.ι (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n) =
      A.arrow ≫ K.X.homologyπ n) :
    ∃ e : cokernel (Subobject.ofLE (B ⊓ Z) Z inf_le_right) ≅
        cokernel (image.preComp
          (HomologicalComplex.homologyMap (K.filtration.diagram.map
            (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) n)
          (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n)),
      a ≫ cokernel.π (Subobject.ofLE (B ⊓ Z) Z inf_le_right) ≫ e.hom =
        b ≫ cokernel.π (image.preComp
          (HomologicalComplex.homologyMap (K.filtration.diagram.map
            (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) n)
          (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n)) :=
  ((exists_iso_stablePage_iff_and_isGLB_isLUB_inducedFiltration_iff K p n F hF A hA _ _ rfl rfl
    (fun p' => Subobject.mk (image.ι
      (HomologicalComplex.homologyMap (K.filtration.ι.app (op p')) n))) (fun _ => rfl)).1
    Z B hZ hB a ha b hb).mpr ⟨hZN, hBD⟩

/-- **The comparison `E_∞^{p, q} ≅ gr^pH^n(K^•)` of [Stacks, Tag 012V], as data.** Where the
inclusions (012S) and (012T) are equalities, the stable page `Z_∞^{p, q}/B_∞^{p, q}` *is* the
graded piece of the filtration induced on cohomology, by the isomorphism compatible with the two
maps out of `A = Ker(d^n) ∩ F^pK^n`.

The definition chooses an isomorphism out of
`CochainComplex.exists_iso_stablePage_of_eq_sup`, but the choice is immaterial: by
`CochainComplex.stablePageIsoGradedPiece_unique` there is exactly one isomorphism satisfying
`CochainComplex.stablePageIsoGradedPiece_spec`, so this *is* the comparison and not a
representative of it.  That is the difference between a chosen isomorphism and a canonical one,
and it is what carrying the comparison across a morphism of filtered complexes needs. -/
noncomputable def stablePageIsoGradedPiece
    (hF : ∀ p' m : ℤ, F p' m = Subobject.mk ((K.filtration.ι.app (op p')).f m))
    (hA : A = (Subobject.pullback (K.X.iCycles n)).obj (F p n))
    (hZ : IsGLB (Set.range fun r : ℕ =>
      F p n ⊓ (Subobject.pullback (K.X.d n (n + 1))).obj (F (p + r) (n + 1)) ⊔ F (p + 1) n) Z)
    (hB : IsLUB (Set.range fun r : ℕ =>
      F p n ⊓ (Subobject.«exists» (K.X.d (n - 1) n)).obj (F (p - r) (n - 1)) ⊔ F (p + 1) n) B)
    (hZN : Z = kernelSubobject (K.X.d n (n + 1)) ⊓ F p n ⊔ F (p + 1) n)
    (hBD : B = imageSubobject (K.X.d (n - 1) n) ⊓ F p n ⊔ F (p + 1) n)
    (a : (A : C) ⟶ (Z : C)) (ha : a ≫ Z.arrow = A.arrow ≫ K.X.iCycles n)
    (b : (A : C) ⟶ image (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n))
    (hb : b ≫ image.ι (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n) =
      A.arrow ≫ K.X.homologyπ n) :
    cokernel (Subobject.ofLE (B ⊓ Z) Z inf_le_right) ≅
      cokernel (image.preComp
        (HomologicalComplex.homologyMap (K.filtration.diagram.map
          (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) n)
        (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n)) :=
  (exists_iso_stablePage_of_eq_sup K p n F A Z B hF hA hZ hB hZN hBD a ha b hb).choose

/-- **The equation characterising `CochainComplex.stablePageIsoGradedPiece`**: it is compatible
with the two maps `a` and `b` out of `A = Ker(d^n) ∩ F^pK^n`. -/
public lemma stablePageIsoGradedPiece_spec
    (hF : ∀ p' m : ℤ, F p' m = Subobject.mk ((K.filtration.ι.app (op p')).f m))
    (hA : A = (Subobject.pullback (K.X.iCycles n)).obj (F p n))
    (hZ : IsGLB (Set.range fun r : ℕ =>
      F p n ⊓ (Subobject.pullback (K.X.d n (n + 1))).obj (F (p + r) (n + 1)) ⊔ F (p + 1) n) Z)
    (hB : IsLUB (Set.range fun r : ℕ =>
      F p n ⊓ (Subobject.«exists» (K.X.d (n - 1) n)).obj (F (p - r) (n - 1)) ⊔ F (p + 1) n) B)
    (hZN : Z = kernelSubobject (K.X.d n (n + 1)) ⊓ F p n ⊔ F (p + 1) n)
    (hBD : B = imageSubobject (K.X.d (n - 1) n) ⊓ F p n ⊔ F (p + 1) n)
    (a : (A : C) ⟶ (Z : C)) (ha : a ≫ Z.arrow = A.arrow ≫ K.X.iCycles n)
    (b : (A : C) ⟶ image (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n))
    (hb : b ≫ image.ι (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n) =
      A.arrow ≫ K.X.homologyπ n) :
    a ≫ cokernel.π (Subobject.ofLE (B ⊓ Z) Z inf_le_right) ≫
        (stablePageIsoGradedPiece K p n F A Z B hF hA hZ hB hZN hBD a ha b hb).hom =
      b ≫ cokernel.π (image.preComp
        (HomologicalComplex.homologyMap (K.filtration.diagram.map
          (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) n)
        (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n)) :=
  (exists_iso_stablePage_of_eq_sup K p n F A Z B hF hA hZ hB hZN hBD a ha b hb).choose_spec

/-- **`CochainComplex.stablePageIsoGradedPiece` is the only isomorphism satisfying
`CochainComplex.stablePageIsoGradedPiece_spec`.** This is what makes the comparison of
[Stacks, Tag 012V] canonical rather than chosen: the equation of (012V) pins it. -/
public lemma stablePageIsoGradedPiece_unique
    (hF : ∀ p' m : ℤ, F p' m = Subobject.mk ((K.filtration.ι.app (op p')).f m))
    (hA : A = (Subobject.pullback (K.X.iCycles n)).obj (F p n))
    (hZ : IsGLB (Set.range fun r : ℕ =>
      F p n ⊓ (Subobject.pullback (K.X.d n (n + 1))).obj (F (p + r) (n + 1)) ⊔ F (p + 1) n) Z)
    (hB : IsLUB (Set.range fun r : ℕ =>
      F p n ⊓ (Subobject.«exists» (K.X.d (n - 1) n)).obj (F (p - r) (n - 1)) ⊔ F (p + 1) n) B)
    (hZN : Z = kernelSubobject (K.X.d n (n + 1)) ⊓ F p n ⊔ F (p + 1) n)
    (hBD : B = imageSubobject (K.X.d (n - 1) n) ⊓ F p n ⊔ F (p + 1) n)
    (a : (A : C) ⟶ (Z : C)) (ha : a ≫ Z.arrow = A.arrow ≫ K.X.iCycles n)
    (b : (A : C) ⟶ image (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n))
    (hb : b ≫ image.ι (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n) =
      A.arrow ≫ K.X.homologyπ n)
    (e : cokernel (Subobject.ofLE (B ⊓ Z) Z inf_le_right) ≅
      cokernel (image.preComp
        (HomologicalComplex.homologyMap (K.filtration.diagram.map
          (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) n)
        (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n)))
    (he : a ≫ cokernel.π (Subobject.ofLE (B ⊓ Z) Z inf_le_right) ≫ e.hom =
      b ≫ cokernel.π (image.preComp
        (HomologicalComplex.homologyMap (K.filtration.diagram.map
          (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) n)
        (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n))) :
    e = stablePageIsoGradedPiece K p n F A Z B hF hA hZ hB hZN hBD a ha b hb :=
  iso_eq_of_comp_cokernel_π_eq_of_eq_sup K p n F A Z B hA hZN
    (le_isLUB_stableBoundaries K p n F B hB) a ha e _ he
    (stablePageIsoGradedPiece_spec K p n F A Z B hF hA hZ hB hZN hBD a ha b hb)

/-! #### The subquotient of [Stacks, Tag 012Q], as data -/

/-- **What dies in `E_∞^{p, q}` dies in `gr^pH^n(K^•)`.** A morphism to
`A = Ker(d^n) ∩ F^pK^n` whose composite with `A ⟶ E_∞^{p, q}` vanishes has vanishing composite
with `A ⟶ gr^pH^n(K^•)`: by (012T) it lands in `Im(d^{n - 1}) ∩ F^pK^n + F^{p + 1}K^n`, so its
class lies in `F^{p + 1}H^n(K^•)`.

This is the computation inside [Stacks, Tag 012Q] that produces the subobject `S` of
`E_∞^{p, q}` and the epimorphism `S ⟶ gr^pH^n(K^•)`. -/
public lemma comp_comp_cokernel_π_preComp_eq_zero
    (hF : ∀ p' m : ℤ, F p' m = Subobject.mk ((K.filtration.ι.app (op p')).f m))
    (hB : IsLUB (Set.range fun r : ℕ =>
      F p n ⊓ (Subobject.«exists» (K.X.d (n - 1) n)).obj (F (p - r) (n - 1)) ⊔ F (p + 1) n) B)
    (a : (A : C) ⟶ (Z : C)) (ha : a ≫ Z.arrow = A.arrow ≫ K.X.iCycles n)
    (b : (A : C) ⟶ image (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n))
    (hb : b ≫ image.ι (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n) =
      A.arrow ≫ K.X.homologyπ n)
    {T : C} (u : T ⟶ (A : C))
    (hu : u ≫ a ≫ cokernel.π (Subobject.ofLE (B ⊓ Z) Z inf_le_right) = 0) :
    u ≫ b ≫ cokernel.π (image.preComp
      (HomologicalComplex.homologyMap (K.filtration.diagram.map
        (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) n)
      (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n)) = 0 := by
  have hBD := isLUB_le_imageSubobject_inf_sup hB
  rw [← Category.assoc]
  refine comp_cokernel_π_image_preComp_eq_zero_of_factors_sup
    (g := K.filtration.diagram.map (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op)
    (f := K.filtration.ι.app (op p)) (h := K.filtration.ι.app (op (p + 1))) (X := K.X)
    (D := imageSubobject (K.X.d (n - 1) n) ⊓ F p n) (y := u ≫ A.arrow) (β := u ≫ b)
    (K.filtration.diagram_map_comp_ι_app _) inf_le_left ?_
    (by rw [Category.assoc, Category.assoc, hb])
  rw [← hF, Category.assoc, ← ha, ← Category.assoc]
  exact Subobject.factors_of_le _ (inf_le_left.trans hBD)
    (factors_of_comp_cokernel_π_ofLE_eq_zero _ _ (by rw [Category.assoc]; exact hu))

/-- **A map `A ⟶ F^pH^n(K^•)` lying over `H^n(K^•)` is an epimorphism**: it is
`CochainComplex.toImageHomologyMap`, by
`CochainComplex.toImageHomologyMap_unique`. -/
public lemma epi_of_comp_image_ι_homologyMap_eq
    (hF : ∀ p' m : ℤ, F p' m = Subobject.mk ((K.filtration.ι.app (op p')).f m))
    (hA : A = (Subobject.pullback (K.X.iCycles n)).obj (F p n))
    (b : (A : C) ⟶ image (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n))
    (hb : b ≫ image.ι (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n) =
      A.arrow ≫ K.X.homologyπ n) :
    Epi b := by
  rw [toImageHomologyMap_unique K p n F A hF hA b hb]
  exact epi_toImageHomologyMap K p n F A hF hA

/-- The kernel of the canonical epimorphism `X ⟶ Im f` is killed by `f`. -/
public lemma kernel_ι_factorThruImageSubobject_comp_eq_zero {X Y : C} (f : X ⟶ Y) :
    kernel.ι (factorThruImageSubobject f) ≫ f = 0 :=
  calc kernel.ι (factorThruImageSubobject f) ≫ f
      = (kernel.ι (factorThruImageSubobject f) ≫ factorThruImageSubobject f) ≫
          (imageSubobject f).arrow := by rw [Category.assoc, imageSubobject_arrow_comp]
    _ = 0 := by rw [kernel.condition, zero_comp]

/-- **The subobject `S` of `E_∞^{p, q}` of [Stacks, Tag 012Q], as data**: the image of
`A = Ker(d^n) ∩ F^pK^n` in `E_∞^{p, q} = Z_∞^{p, q}/B_∞^{p, q}`.  It is the whole of
`E_∞^{p, q}` exactly where the inclusion (012S) is an equality, by
`CochainComplex.epi_comp_cokernel_π_ofLE_of_eq_sup`. -/
noncomputable def stablePageImage (a : (A : C) ⟶ (Z : C)) :
    Subobject (cokernel (Subobject.ofLE (B ⊓ Z) Z inf_le_right)) :=
  imageSubobject (a ≫ cokernel.π (Subobject.ofLE (B ⊓ Z) Z inf_le_right))

/-- **The epimorphism `A ⟶ S` of [Stacks, Tag 012Q], as data.** -/
noncomputable def toStablePageImage (a : (A : C) ⟶ (Z : C)) :
    (A : C) ⟶ (stablePageImage K n A Z B a : C) :=
  factorThruImageSubobject (a ≫ cokernel.π (Subobject.ofLE (B ⊓ Z) Z inf_le_right))

/-- `CochainComplex.toStablePageImage` is an epimorphism. -/
public lemma epi_toStablePageImage (a : (A : C) ⟶ (Z : C)) :
    Epi (toStablePageImage K n A Z B a) :=
  inferInstanceAs (Epi (factorThruImageSubobject
    (a ≫ cokernel.π (Subobject.ofLE (B ⊓ Z) Z inf_le_right))))

/-- The equation characterising `CochainComplex.toStablePageImage`: it lies over
`E_∞^{p, q}`. -/
public lemma toStablePageImage_comp_arrow (a : (A : C) ⟶ (Z : C)) :
    toStablePageImage K n A Z B a ≫ (stablePageImage K n A Z B a).arrow =
      a ≫ cokernel.π (Subobject.ofLE (B ⊓ Z) Z inf_le_right) :=
  imageSubobject_arrow_comp _

/-- **`CochainComplex.toStablePageImage` is the only map `A ⟶ S` over `E_∞^{p, q}`**, because
`S` is a subobject. -/
public lemma toStablePageImage_unique (a : (A : C) ⟶ (Z : C))
    (g : (A : C) ⟶ (stablePageImage K n A Z B a : C))
    (hg : g ≫ (stablePageImage K n A Z B a).arrow =
      a ≫ cokernel.π (Subobject.ofLE (B ⊓ Z) Z inf_le_right)) :
    g = toStablePageImage K n A Z B a :=
  (cancel_mono (stablePageImage K n A Z B a).arrow).1
    (by rw [hg, toStablePageImage_comp_arrow])

/-- **The epimorphism `S ⟶ gr^pH^n(K^•)` of [Stacks, Tag 012Q], as data.** The map `A ⟶ S` is an
epimorphism which kills everything that the map `A ⟶ gr^pH^n(K^•)` kills
(`CochainComplex.comp_comp_cokernel_π_preComp_eq_zero`), so the latter descends to `S`. -/
noncomputable def stablePageImageToGradedPiece
    (hF : ∀ p' m : ℤ, F p' m = Subobject.mk ((K.filtration.ι.app (op p')).f m))
    (hB : IsLUB (Set.range fun r : ℕ =>
      F p n ⊓ (Subobject.«exists» (K.X.d (n - 1) n)).obj (F (p - r) (n - 1)) ⊔ F (p + 1) n) B)
    (a : (A : C) ⟶ (Z : C)) (ha : a ≫ Z.arrow = A.arrow ≫ K.X.iCycles n)
    (b : (A : C) ⟶ image (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n))
    (hb : b ≫ image.ι (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n) =
      A.arrow ≫ K.X.homologyπ n) :
    (stablePageImage K n A Z B a : C) ⟶ cokernel (image.preComp
      (HomologicalComplex.homologyMap (K.filtration.diagram.map
        (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) n)
      (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n)) :=
  Abelian.epiDesc
    (factorThruImageSubobject (a ≫ cokernel.π (Subobject.ofLE (B ⊓ Z) Z inf_le_right)))
    (b ≫ cokernel.π (image.preComp
      (HomologicalComplex.homologyMap (K.filtration.diagram.map
        (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) n)
      (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n)))
    (comp_comp_cokernel_π_preComp_eq_zero K p n F A Z B hF hB a ha b hb
      (kernel.ι (factorThruImageSubobject
        (a ≫ cokernel.π (Subobject.ofLE (B ⊓ Z) Z inf_le_right))))
      (kernel_ι_factorThruImageSubobject_comp_eq_zero _))

/-- The equation characterising `CochainComplex.stablePageImageToGradedPiece`: it is compatible
with the two maps out of `A = Ker(d^n) ∩ F^pK^n`. -/
public lemma toStablePageImage_comp_stablePageImageToGradedPiece
    (hF : ∀ p' m : ℤ, F p' m = Subobject.mk ((K.filtration.ι.app (op p')).f m))
    (hB : IsLUB (Set.range fun r : ℕ =>
      F p n ⊓ (Subobject.«exists» (K.X.d (n - 1) n)).obj (F (p - r) (n - 1)) ⊔ F (p + 1) n) B)
    (a : (A : C) ⟶ (Z : C)) (ha : a ≫ Z.arrow = A.arrow ≫ K.X.iCycles n)
    (b : (A : C) ⟶ image (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n))
    (hb : b ≫ image.ι (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n) =
      A.arrow ≫ K.X.homologyπ n) :
    toStablePageImage K n A Z B a ≫
        stablePageImageToGradedPiece K p n F A Z B hF hB a ha b hb =
      b ≫ cokernel.π (image.preComp
        (HomologicalComplex.homologyMap (K.filtration.diagram.map
          (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) n)
        (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n)) := by
  have := epi_toStablePageImage K n A Z B a
  exact Abelian.comp_epiDesc _ _ _

/-- `CochainComplex.stablePageImageToGradedPiece` is an epimorphism: this is the conclusion of
[Stacks, Tag 012Q] that `gr^pH^n(K^•)` is a quotient of the subobject `S` of `E_∞^{p, q}`. -/
public lemma epi_stablePageImageToGradedPiece
    (hF : ∀ p' m : ℤ, F p' m = Subobject.mk ((K.filtration.ι.app (op p')).f m))
    (hA : A = (Subobject.pullback (K.X.iCycles n)).obj (F p n))
    (hB : IsLUB (Set.range fun r : ℕ =>
      F p n ⊓ (Subobject.«exists» (K.X.d (n - 1) n)).obj (F (p - r) (n - 1)) ⊔ F (p + 1) n) B)
    (a : (A : C) ⟶ (Z : C)) (ha : a ≫ Z.arrow = A.arrow ≫ K.X.iCycles n)
    (b : (A : C) ⟶ image (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n))
    (hb : b ≫ image.ι (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n) =
      A.arrow ≫ K.X.homologyπ n) :
    Epi (stablePageImageToGradedPiece K p n F A Z B hF hB a ha b hb) := by
  have : Epi b := epi_of_comp_image_ι_homologyMap_eq K p n F A hF hA b hb
  have hcomp : Epi (toStablePageImage K n A Z B a ≫
      stablePageImageToGradedPiece K p n F A Z B hF hB a ha b hb) := by
    rw [toStablePageImage_comp_stablePageImageToGradedPiece]
    exact epi_comp _ _
  exact epi_of_epi (toStablePageImage K n A Z B a) _

/-- **`CochainComplex.stablePageImageToGradedPiece` is the only map `S ⟶ gr^pH^n(K^•)`
compatible with the maps out of `A`**, because `A ⟶ S` is an epimorphism. -/
public lemma stablePageImageToGradedPiece_unique
    (hF : ∀ p' m : ℤ, F p' m = Subobject.mk ((K.filtration.ι.app (op p')).f m))
    (hB : IsLUB (Set.range fun r : ℕ =>
      F p n ⊓ (Subobject.«exists» (K.X.d (n - 1) n)).obj (F (p - r) (n - 1)) ⊔ F (p + 1) n) B)
    (a : (A : C) ⟶ (Z : C)) (ha : a ≫ Z.arrow = A.arrow ≫ K.X.iCycles n)
    (b : (A : C) ⟶ image (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n))
    (hb : b ≫ image.ι (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n) =
      A.arrow ≫ K.X.homologyπ n)
    (e : (stablePageImage K n A Z B a : C) ⟶ cokernel (image.preComp
      (HomologicalComplex.homologyMap (K.filtration.diagram.map
        (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) n)
      (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n)))
    (he : toStablePageImage K n A Z B a ≫ e =
      b ≫ cokernel.π (image.preComp
        (HomologicalComplex.homologyMap (K.filtration.diagram.map
          (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) n)
        (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n))) :
    e = stablePageImageToGradedPiece K p n F A Z B hF hB a ha b hb := by
  have := epi_toStablePageImage K n A Z B a
  refine (cancel_epi (toStablePageImage K n A Z B a)).1 ?_
  rw [he, toStablePageImage_comp_stablePageImageToGradedPiece]


end StableComparison


/-- The presentations `Z_r^{p, q}` and `D_r^{p, q}` of the pages are the model cycles and
boundaries of `FilteredComplexSpectralSequence`. -/
private theorem eq_cycles_and_boundaries
    {A : Type u} [Category.{v} A] [Abelian A]
    (K : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ)
    (F : ∀ (_p n : ℤ), Subobject (K.X.X n))
    (Z : ∀ (_r _p n : ℤ), Subobject (K.X.X n))
    (hZ : ∀ r p n : ℤ, Z r p n =
      F p n ⊓ (Subobject.pullback (K.X.d n (n + 1))).obj (F (p + r) (n + 1)))
    (D : ∀ (_r _p n : ℤ), Subobject (K.X.X n))
    (hD : ∀ r p n : ℤ, D r p n = Z (r - 1) (p + 1) n ⊔
      (Subobject.«exists» (K.X.d (n - 1) n)).obj (Z (r - 1) (p - r + 1) (n - 1))) :
    Z = FilteredComplexSpectralSequence.cycles K.X F ∧
      D = FilteredComplexSpectralSequence.boundaries K.X F := by
  obtain rfl : Z = FilteredComplexSpectralSequence.cycles K.X F := by
    funext r p n; exact hZ r p n
  exact ⟨rfl, by funext r p n; exact hD r p n⟩

/-- **Stacks 012W.** Let `𝒜` be an abelian category and let `(K^•, F)` be a filtered complex of
`𝒜` whose filtration is finite in each degree. Let `E` be the spectral sequence of `(K^•, F)`,
so that its page at `(r, p, q)` is `Z_r^{p,q}/D_r^{p,q}` for `n = p + q`, where
`Z_r^{p,q} = F^p K^n ⊓ (d^n)⁻¹(F^{p+r}K^{n+1})` and
`D_r^{p,q} = Z_{r-1}^{p+1,q-1} ⊔ d^{n-1}(Z_{r-1}^{p-r+1,q+r-2})`, and let
`F^p H^n(K^•) = Im(H^n(F^pK^•) ⟶ H^n(K^•))` be the induced filtration on cohomology. Then:

1. `E` is bounded: for every `n` only finitely many `E_0^{p, n-p}` are nonzero;
2. the induced filtration on each `H^n(K^•)` is finite;
3. `E` converges to `H^*(K^•)`: it is regular, `d_r^{p,q} = 0` for `r ≫ 0`, and it converges
   weakly, the stable cycles and boundaries `Z_∞^{p,q}` and `B_∞^{p,q}` existing and being equal
   to `Ker(d^n) ⊓ F^p K^n ⊔ F^{p+1}K^n` and `Im(d^{n-1}) ⊓ F^p K^n ⊔ F^{p+1}K^n`, i.e. equality
   holding in (012S) and (012T);
4. if `𝒞 ⊆ 𝒜` is a weak Serre subcategory with `E_r^{p,q}` in `𝒞` for all `p, q` and some
   `r ≥ 0`, then every `H^n(K^•)` is in `𝒞`. -/
@[stacks 012W, ega "0 11.2.4" "special case"]
public theorem isBounded_and_converges_of_isDegreewiseFinite
    {A : Type u} [Category.{v} A] [Abelian A]
    (K : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ)
    (hK : K.filtration.IsDegreewiseFinite)
    (F : ∀ (_p n : ℤ), Subobject (K.X.X n))
    (hF : ∀ p n : ℤ, F p n = Subobject.mk ((K.filtration.ι.app (op p)).f n))
    (Z : ∀ (_r _p n : ℤ), Subobject (K.X.X n))
    (hZ : ∀ r p n : ℤ, Z r p n =
      F p n ⊓ (Subobject.pullback (K.X.d n (n + 1))).obj (F (p + r) (n + 1)))
    (D : ∀ (_r _p n : ℤ), Subobject (K.X.X n))
    (hD : ∀ r p n : ℤ, D r p n = Z (r - 1) (p + 1) n ⊔
      (Subobject.«exists» (K.X.d (n - 1) n)).obj (Z (r - 1) (p - r + 1) (n - 1)))
    (FH : ∀ (n _p : ℤ), Subobject (K.X.homology n))
    (hFH : ∀ n p : ℤ, FH n p =
      imageSubobject (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n))
    (E : CohomologicalSpectralSequence A 0)
    (hE : ∀ (r p q n : ℤ) (hr : 0 ≤ r) (_ : n = p + q), (E.page r hr).X (p, q) ≅
      cokernel (Subobject.ofLE _ _ (inf_le_right : D r p n ⊓ Z r p n ≤ Z r p n))) :
    (∀ n : ℤ, {p : ℤ | ¬ IsZero ((E.page 0).X (p, n - p))}.Finite) ∧
    (∀ n : ℤ, ∃ a b : ℤ, a ≤ b ∧ FH n a = ⊤ ∧ FH n b = ⊥) ∧
    (∀ p q : ℤ, ∃ b : ℤ, ∀ (r : ℤ) (hr : 0 ≤ r), b ≤ r →
      (E.page r hr).d (p, q) (p + r, q - r + 1) = 0) ∧
    (∀ p n : ℤ,
      IsGLB (Set.range fun r : ℕ =>
          F p n ⊓ (Subobject.pullback (K.X.d n (n + 1))).obj (F (p + r) (n + 1)) ⊔ F (p + 1) n)
        (kernelSubobject (K.X.d n (n + 1)) ⊓ F p n ⊔ F (p + 1) n) ∧
      IsLUB (Set.range fun r : ℕ =>
          F p n ⊓ (Subobject.«exists» (K.X.d (n - 1) n)).obj (F (p - r) (n - 1)) ⊔ F (p + 1) n)
        (imageSubobject (K.X.d (n - 1) n) ⊓ F p n ⊔ F (p + 1) n)) ∧
    (∀ (P : ObjectProperty A) [P.IsWeakSerreClass] (r : ℤ) (hr : 0 ≤ r),
      (∀ p q : ℤ, P ((E.page r hr).X (p, q))) → ∀ n : ℤ, P (K.X.homology n)) := by
  have himKer : ∀ n : ℤ, imageSubobject (K.X.d (n - 1) n) ≤ kernelSubobject (K.X.d n (n + 1)) :=
    fun n => image_le_kernel _ _ (by simp)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- (1) boundedness: `E_0^{p, n - p} = gr^p K^n` vanishes where the filtration does not jump.
    intro n
    obtain ⟨a, ha⟩ := exists_F_eq_top K F hF hK n
    obtain ⟨b, hb⟩ := exists_F_eq_bot K F hF hK n
    refine Set.Finite.subset (Set.finite_Ico a b) fun p hp => ?_
    by_contra hmem
    simp only [Set.mem_Ico, not_and, not_lt] at hmem
    refine hp (Filtered.isZero_page K Z D E hE 0 p (n - p) n le_rfl (by ring) (le_of_eq ?_))
    rw [Z_eq_F K F hF Z hZ le_rfl p n, D_zero_eq_F K F hF Z hZ D hD p n]
    rcases lt_or_ge p a with hlt | hge
    · rw [ha (p + 1) (by omega), ha p (by omega)]
    · rw [hb (p + 1) (by omega : b ≤ p + 1), hb p (hmem hge)]
  · -- (2) the induced filtration on `H^n(K^•)` is finite: `F^a K^• ⟶ K^•` is a quasi-isomorphism
    -- at `n` once `F^a` is everything in the degrees `n - 1, n, n + 1`.
    intro n
    obtain ⟨a₁, ha₁⟩ := exists_F_eq_top K F hF hK (n - 1)
    obtain ⟨a₂, ha₂⟩ := exists_F_eq_top K F hF hK n
    obtain ⟨a₃, ha₃⟩ := exists_F_eq_top K F hF hK (n + 1)
    obtain ⟨b₀, hb₀⟩ := exists_F_eq_bot K F hF hK n
    set a : ℤ := min a₁ (min a₂ a₃) with hadef
    refine ⟨a, max a b₀, le_max_left _ _, ?_, ?_⟩
    · have := CochainComplex.isIso_homologyMap_of_isIso_f (K.filtration.ι.app (op a)) n
        ((F_eq_top_iff K F hF a (n - 1)).mp (ha₁ a (by omega)))
        ((F_eq_top_iff K F hF a n).mp (ha₂ a (by omega)))
        ((F_eq_top_iff K F hF a (n + 1)).mp (ha₃ a (by omega)))
      rw [hFH n a]
      exact Subobject.imageSubobject_eq_top_of_epi _
    · have hzero : IsZero ((K.filtration.diagram.obj (op (max a b₀))).X n) := by
        refine IsZero.of_mono_eq_zero ((K.filtration.ι.app (op (max a b₀))).f n) ?_
        rw [← Subobject.mk_eq_bot_iff_zero, ← hF]
        exact hb₀ _ (le_max_right _ _)
      rw [hFH n (max a b₀), show HomologicalComplex.homologyMap
        (K.filtration.ι.app (op (max a b₀))) n = 0 from
        (ShortComplex.isZero_homology_of_isZero_X₂ _ hzero).eq_of_src _ _, imageSubobject_zero]
  · -- (3) regularity: the target of `d_r^{p,q}` vanishes for `r ≫ 0`.
    intro p q
    obtain ⟨b, hb⟩ := exists_F_eq_bot K F hF hK (p + q + 1)
    refine ⟨b - p, fun r hr hbr => IsZero.eq_of_tgt (Filtered.isZero_page K Z D E hE r (p + r)
      (q - r + 1) (p + q + 1) hr (by ring) ?_) _ _⟩
    rw [Z_eq_bot K F Z hZ (hb (p + r) (by omega))]
    exact bot_le
  · -- (4) the two equalities (012S) and (012T): at `r ≫ 0` the `r`-th member of each family
    -- already is the asserted bound.
    intro p n
    obtain ⟨b, hb⟩ := exists_F_eq_bot K F hF hK (n + 1)
    obtain ⟨a, ha⟩ := exists_F_eq_top K F hF hK (n - 1)
    constructor
    · refine IsLeast.isGLB ⟨Set.mem_range.2 ⟨(b - p).toNat, ?_⟩,
        mem_lowerBounds.2 (Set.forall_mem_range.2 fun r => ?_)⟩
      · rw [hb _ (by omega : b ≤ p + ((b - p).toNat : ℤ)), Subobject.pullback_bot, inf_comm]
      · refine sup_le_sup_right (le_inf inf_le_right (inf_le_left.trans ?_)) _
        rw [← Subobject.pullback_bot]
        exact (Subobject.pullback _).monotone bot_le
    · refine IsGreatest.isLUB ⟨Set.mem_range.2 ⟨(p - a).toNat, ?_⟩,
        mem_upperBounds.2 (Set.forall_mem_range.2 fun r => ?_)⟩
      · rw [ha _ (by omega : p - ((p - a).toNat : ℤ) ≤ a), Subobject.exists_obj_top, inf_comm]
      · refine sup_le_sup_right (le_inf (inf_le_right.trans ?_) inf_le_left) _
        rw [← Subobject.exists_obj_top]
        exact (Subobject.exists _).monotone le_top
  · -- (4) of the source: a weak Serre subcategory containing one whole page contains every
    -- `H^n(K^•)`. The filtration used on `H^n(K^•)` is by the images of `Ker(d^n) ⊓ F^p K^n`,
    -- whose graded piece at `p` is `E_r^{p, n - p}` for any `r` large enough in the sense of
    -- `Z_eq_kernelSubobject_inf` and `D_eq_sup`.
    intro P _ r hr hpage n
    obtain ⟨a₀, ha₀⟩ := exists_F_eq_top K F hF hK n
    obtain ⟨b₀, hb₀⟩ := exists_F_eq_bot K F hF hK n
    obtain ⟨a₁, ha₁⟩ := exists_F_eq_top K F hF hK (n - 1)
    obtain ⟨b₁, hb₁⟩ := exists_F_eq_bot K F hF hK (n + 1)
    refine prop_homology_of_prop_gradedPiece K.X n P
      (fun p => kernelSubobject (K.X.d n (n + 1)) ⊓ F p n)
      (fun p => arrow_comp_d_eq_zero_of_le inf_le_left (kernelSubobject_arrow_comp _))
      (fun p => inf_le_inf_left _ (F_antitone K F hF (by omega : p ≤ p + 1) n))
      a₀ (max a₀ b₀) (le_max_left _ _) (le_inf le_rfl (by rw [ha₀ a₀ le_rfl]; exact le_top))
      (by rw [hb₀ _ (le_max_right _ _), inf_bot_eq]) fun p => ?_
    obtain ⟨r', hr'0, hr'r, hr'b, hr'a⟩ : ∃ r' : ℤ, 0 ≤ r' ∧ r ≤ r' ∧ b₁ ≤ p + r' ∧
        p - r' + 1 ≤ a₁ :=
      ⟨max (max r 0) (max (b₁ - p) (p + 1 - a₁)), by omega, by omega, by omega, by omega⟩
    have hZeq : Z r' p n = kernelSubobject (K.X.d n (n + 1)) ⊓ F p n :=
      Z_eq_kernelSubobject_inf K F Z hZ (hb₁ _ hr'b)
    have hDeq : D r' p n = kernelSubobject (K.X.d n (n + 1)) ⊓ F (p + 1) n ⊔
        imageSubobject (K.X.d (n - 1) n) ⊓ F p n :=
      D_eq_sup K F Z hZ D hD (hb₁ _ hr'b) (ha₁ _ hr'a)
    have hDle : D r' p n ≤ Z r' p n := by
      rw [hZeq, hDeq]
      exact sup_le (le_inf inf_le_left (inf_le_right.trans
          (F_antitone K F hF (by omega : p ≤ p + 1) n)))
        (le_inf (inf_le_left.trans (himKer n)) inf_le_right)
    refine prop_cokernel_ofLE_congr P _ _ ?_ hZeq
      (P.prop_of_iso (hE r' p (n - p) n hr'0 (by ring))
        (prop_page_of_le E P hr (fun pq => hpage pq.1 pq.2) r' hr'r hr'0 (p, n - p)))
    rw [inf_eq_left.mpr hDle, hDeq, ← inf_assoc, inf_eq_left.mpr (himKer n)]

/-! ### Convergence from eventual control of the cohomology of the filtration -/

private lemma image_homologyMap_eq_bot_of_isZero
    {A : Type u} [Category.{v} A] [Abelian A]
    {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℤ)
    (h : IsZero (K.homology n)) :
    imageSubobject (HomologicalComplex.homologyMap f n) = ⊥ := by
  rw [show HomologicalComplex.homologyMap f n = 0 from h.eq_of_src _ _]
  exact imageSubobject_zero

/-- Eventual vanishing and eventual surjectivity on homology give a finite induced filtration. -/
private lemma inducedFiltration_isFinite
    {A : Type u} [Category.{v} A] [Abelian A]
    (K : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ)
    (FH : ∀ (n _p : ℤ), Subobject (K.X.homology n))
    (hFH : ∀ n p : ℤ, FH n p =
      imageSubobject (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n))
    (n : ℤ)
    (hzero : ∃ b : ℤ, ∀ p : ℤ, b ≤ p →
      IsZero ((K.filtration.obj (op p)).homology n))
    (hiso : ∃ a : ℤ, ∀ p : ℤ, p ≤ a →
      IsIso (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n)) :
    ∃ a b : ℤ, a ≤ b ∧ FH n a = ⊤ ∧ FH n b = ⊥ := by
  obtain ⟨a, ha⟩ := hiso
  obtain ⟨b, hb⟩ := hzero
  refine ⟨a, max a b, le_max_left _ _, ?_, ?_⟩
  · have := ha a le_rfl
    rw [hFH]
    exact Subobject.imageSubobject_eq_top_of_epi _
  · rw [hFH]
    exact image_homologyMap_eq_bot_of_isZero _ _ (hb _ (le_max_right _ _))

/-- If two filtration inclusions induce isomorphisms on homology, so does their transition. -/
private lemma isIso_homologyMap_filtration_map
    {A : Type u} [Category.{v} A] [Abelian A]
    (K : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ) (n : ℤ)
    {p p' : ℤ} (h : p ≤ p')
    [IsIso (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n)]
    [IsIso (HomologicalComplex.homologyMap (K.filtration.ι.app (op p')) n)] :
    IsIso (HomologicalComplex.homologyMap
      (K.filtration.diagram.map (homOfLE h).op) n) := by
  have hcomp : HomologicalComplex.homologyMap
      (K.filtration.diagram.map (homOfLE h).op) n ≫
        HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n =
      HomologicalComplex.homologyMap (K.filtration.ι.app (op p')) n := by
    rw [← HomologicalComplex.homologyMap_comp]
    congr 1
    exact K.filtration.diagram_map_comp_ι_app _
  exact IsIso.of_isIso_fac_right hcomp

/-- Adjacent filtration steps have the same homology outside a finite interval. -/
private lemma isIso_homologyMap_filtration_map_outside_interval
    {A : Type u} [Category.{v} A] [Abelian A]
    (K : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ)
    (hzero : ∀ n : ℤ, ∃ b : ℤ, ∀ p : ℤ, b ≤ p →
      IsZero ((K.filtration.obj (op p)).homology n))
    (hiso : ∀ n : ℤ, ∃ a : ℤ, ∀ p : ℤ, p ≤ a →
      IsIso (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n))
    (n : ℤ) :
    ∃ a b : ℤ, ∀ p : ℤ, p < a ∨ b ≤ p →
      IsIso (HomologicalComplex.homologyMap (K.filtration.diagram.map
        (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) n) ∧
      IsIso (HomologicalComplex.homologyMap (K.filtration.diagram.map
        (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) (n + 1)) := by
  obtain ⟨a₀, ha₀⟩ := hiso n
  obtain ⟨a₁, ha₁⟩ := hiso (n + 1)
  obtain ⟨b₀, hb₀⟩ := hzero n
  obtain ⟨b₁, hb₁⟩ := hzero (n + 1)
  refine ⟨min a₀ a₁, max b₀ b₁, fun p hp => ?_⟩
  rcases hp with hp | hp
  · have := ha₀ p (by omega)
    have := ha₀ (p + 1) (by omega)
    have := ha₁ p (by omega)
    have := ha₁ (p + 1) (by omega)
    exact ⟨isIso_homologyMap_filtration_map K n _,
      isIso_homologyMap_filtration_map K (n + 1) _⟩
  · exact ⟨(hb₀ (p + 1) (by omega)).isIso (hb₀ p (by omega)) _,
      (hb₁ (p + 1) (by omega)).isIso (hb₁ p (by omega)) _⟩

/-- Finite diagonal support on any page implies eventual vanishing of each differential. -/
private lemma differential_eq_zero_of_finite_diagonal
    {A : Type u} [Category.{v} A] [Abelian A]
    {r₀ : ℤ} (E : CohomologicalSpectralSequence A r₀)
    (s : ℤ) (hs : r₀ ≤ s)
    (hfinite : ∀ n : ℤ, {p : ℤ | ¬ IsZero ((E.page s hs).X (p, n - p))}.Finite)
    (p q : ℤ) :
    ∃ b : ℤ, ∀ (r : ℤ) (hr : r₀ ≤ r), b ≤ r →
      (E.page r hr).d (p, q) (p + r, q - r + 1) = 0 := by
  obtain ⟨b, hb⟩ := (hfinite (p + q + 1)).bddAbove
  refine ⟨max s (b - p + 1), fun r hr hbr => ?_⟩
  have hz : IsZero ((E.page s hs).X (p + r, q - r + 1)) := by
    by_contra h
    have hmem : p + r ∈ {i : ℤ | ¬ IsZero
        ((E.page s hs).X (i, p + q + 1 - i))} := by
      simpa only [Set.mem_ofPred_eq, show p + q + 1 - (p + r) = q - r + 1 by omega] using h
    have := hb hmem
    omega
  exact (SpectralSequence.isZero_page_of_le E hs _ hz r (by omega) hr).eq_of_tgt _ _

/-- The stable-cycle and stable-boundary equalities give the canonical comparison isomorphism. -/
private lemma exists_iso_of_stable_cycles_boundaries
    {A : Type u} [Category.{v} A] [Abelian A]
    (K : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ)
    (F : ∀ (_p n : ℤ), Subobject (K.X.X n))
    (hF : ∀ p n : ℤ, F p n = Subobject.mk ((K.filtration.ι.app (op p)).f n))
    (p n : ℤ)
    (hstable : IsGLB (Set.range fun r : ℕ ↦
          F p n ⊓ (Subobject.pullback (K.X.d n (n + 1))).obj (F (p + r) (n + 1)) ⊔
            F (p + 1) n)
        (kernelSubobject (K.X.d n (n + 1)) ⊓ F p n ⊔ F (p + 1) n) ∧
      IsLUB (Set.range fun r : ℕ ↦
          F p n ⊓ (Subobject.«exists» (K.X.d (n - 1) n)).obj (F (p - r) (n - 1)) ⊔
            F (p + 1) n)
        (imageSubobject (K.X.d (n - 1) n) ⊓ F p n ⊔ F (p + 1) n)) :
    let C := (Subobject.pullback (K.X.iCycles n)).obj (F p n)
    let N := kernelSubobject (K.X.d n (n + 1)) ⊓ F p n ⊔ F (p + 1) n
    let B := imageSubobject (K.X.d (n - 1) n) ⊓ F p n ⊔ F (p + 1) n
    ∃ (a : (C : A) ⟶ (N : A))
      (b : (C : A) ⟶ image (HomologicalComplex.homologyMap
        (K.filtration.ι.app (op p)) n))
      (e : cokernel (Subobject.ofLE (B ⊓ N) N inf_le_right) ≅
        cokernel (image.preComp
          (HomologicalComplex.homologyMap (K.filtration.diagram.map
            (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) n)
          (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n))),
      C.arrow ≫ K.X.iCycles n = a ≫ N.arrow ∧
      C.arrow ≫ K.X.homologyπ n =
        b ≫ image.ι (HomologicalComplex.homologyMap
          (K.filtration.ι.app (op p)) n) ∧
      a ≫ cokernel.π (Subobject.ofLE (B ⊓ N) N inf_le_right) ≫ e.hom =
        b ≫ cokernel.π (image.preComp
          (HomologicalComplex.homologyMap (K.filtration.diagram.map
            (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) n)
          (HomologicalComplex.homologyMap
            (K.filtration.ι.app (op p)) n)) := by
  dsimp only
  let C := (Subobject.pullback (K.X.iCycles n)).obj (F p n)
  let N := kernelSubobject (K.X.d n (n + 1)) ⊓ F p n ⊔ F (p + 1) n
  let B := imageSubobject (K.X.d (n - 1) n) ⊓ F p n ⊔ F (p + 1) n
  have hCF : (F p n).Factors (C.arrow ≫ K.X.iCycles n) :=
    (pullback_factors_iff _ _ _).mp (Subobject.factors_self C)
  have hCN : N.Factors (C.arrow ≫ K.X.iCycles n) :=
    Subobject.sup_factors_of_factors_left ((Subobject.inf_factors _).mpr
      ⟨kernelSubobject_factors _ _ (by simp), hCF⟩)
  let a : (C : A) ⟶ (N : A) := N.factorThru _ hCN
  have ha : a ≫ N.arrow = C.arrow ≫ K.X.iCycles n := N.factorThru_arrow _ hCN
  obtain ⟨b, _, hb⟩ := exists_epi_comp_image_ι_homologyMap (X := K.X)
    (K.filtration.ι.app (op p)) n C (by dsimp only [C]; rw [hF])
  obtain ⟨e, he⟩ :=
    ((CochainComplex.exists_iso_stablePage_iff_and_isGLB_isLUB_inducedFiltration_iff
      K p n F hF C rfl N B rfl rfl
      (fun p' => imageSubobject (HomologicalComplex.homologyMap
        (K.filtration.ι.app (op p')) n)) (fun _ => rfl)).1
      N B hstable.1 hstable.2 a ha b hb).mpr ⟨rfl, rfl⟩
  exact ⟨a, b, e, ha.symm, hb.symm, he⟩

/-- **Stacks 0BK5.** Let `𝒜` be an abelian category and let `(K^•, F)` be a filtered complex of
`𝒜` such that, for every `n`, `H^n(F^pK^•) = 0` for `p ≫ 0` and `H^n(F^pK^•) ⟶ H^n(K^•)` is an
isomorphism for `p ≪ 0`. Let `E` be the spectral sequence of `(K^•, F)`, presented as in
`isBounded_and_converges_of_isDegreewiseFinite` by its pages `Z_r^{p,q}/D_r^{p,q}`, and let
`F^p H^n(K^•) = Im(H^n(F^pK^•) ⟶ H^n(K^•))`. Then:

1. `E` is bounded: for every `n` only finitely many `E_1^{p, n-p}` are nonzero;
2. the induced filtration on each `H^n(K^•)` is finite;
3. `E` converges to `H^*(K^•)`: it is regular, the stable cycles and boundaries exist and equality
   holds in (012S) and (012T), and the resulting canonical comparison
   `E_∞^{p, n-p} ≅ gr^p H^n(K^•)` of [Stacks, Tag 012V] is an isomorphism.

Boundedness is stated on the first page, where the source's proof establishes it: under these
hypotheses `E_0^{p, q} = gr^p K^{p+q}` need not vanish for `|p| ≫ 0` (take any acyclic complex
with a nowhere-stationary filtration by acyclic subcomplexes), so the source's spectral sequence
is bounded as a spectral sequence starting at `r = 1`. -/
@[stacks 0BK5, ega "0 13.6.4" "partial"]
public theorem isBounded_and_converges_of_eventually_isZero_of_eventually_isIso
    {A : Type u} [Category.{v} A] [Abelian A]
    (K : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ)
    (F : ∀ (_p n : ℤ), Subobject (K.X.X n))
    (hF : ∀ p n : ℤ, F p n = Subobject.mk ((K.filtration.ι.app (op p)).f n))
    (Z : ∀ (_r _p n : ℤ), Subobject (K.X.X n))
    (hZ : ∀ r p n : ℤ, Z r p n =
      F p n ⊓ (Subobject.pullback (K.X.d n (n + 1))).obj (F (p + r) (n + 1)))
    (D : ∀ (_r _p n : ℤ), Subobject (K.X.X n))
    (hD : ∀ r p n : ℤ, D r p n = Z (r - 1) (p + 1) n ⊔
      (Subobject.«exists» (K.X.d (n - 1) n)).obj (Z (r - 1) (p - r + 1) (n - 1)))
    (FH : ∀ (n _p : ℤ), Subobject (K.X.homology n))
    (hFH : ∀ n p : ℤ, FH n p =
      imageSubobject (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n))
    (E : CohomologicalSpectralSequence A 0)
    (hE : ∀ (r p q n : ℤ) (hr : 0 ≤ r) (_ : n = p + q), (E.page r hr).X (p, q) ≅
      cokernel (Subobject.ofLE _ _ (inf_le_right : D r p n ⊓ Z r p n ≤ Z r p n)))
    (hzero : ∀ n : ℤ, ∃ p₀ : ℤ, ∀ p : ℤ, p₀ ≤ p →
      IsZero ((K.filtration.obj (op p)).homology n))
    (hiso : ∀ n : ℤ, ∃ p₁ : ℤ, ∀ p : ℤ, p ≤ p₁ →
      IsIso (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n)) :
    (∀ n : ℤ, {p : ℤ | ¬ IsZero ((E.page 1 (by omega)).X (p, n - p))}.Finite) ∧
    (∀ n : ℤ, ∃ a b : ℤ, a ≤ b ∧ FH n a = ⊤ ∧ FH n b = ⊥) ∧
    (∀ p q : ℤ, ∃ b : ℤ, ∀ (r : ℤ) (hr : 0 ≤ r), b ≤ r →
      (E.page r hr).d (p, q) (p + r, q - r + 1) = 0) ∧
    (∀ p n : ℤ,
      IsGLB (Set.range fun r : ℕ =>
          F p n ⊓ (Subobject.pullback (K.X.d n (n + 1))).obj (F (p + r) (n + 1)) ⊔
            F (p + 1) n)
        (kernelSubobject (K.X.d n (n + 1)) ⊓ F p n ⊔ F (p + 1) n) ∧
      IsLUB (Set.range fun r : ℕ =>
          F p n ⊓ (Subobject.«exists» (K.X.d (n - 1) n)).obj (F (p - r) (n - 1)) ⊔
            F (p + 1) n)
        (imageSubobject (K.X.d (n - 1) n) ⊓ F p n ⊔ F (p + 1) n)) ∧
    (∀ p n : ℤ,
      let C := (Subobject.pullback (K.X.iCycles n)).obj (F p n)
      let N := kernelSubobject (K.X.d n (n + 1)) ⊓ F p n ⊔ F (p + 1) n
      let B := imageSubobject (K.X.d (n - 1) n) ⊓ F p n ⊔ F (p + 1) n
      ∃ (a : (C : A) ⟶ (N : A))
        (b : (C : A) ⟶ image (HomologicalComplex.homologyMap
          (K.filtration.ι.app (op p)) n))
        (e : cokernel (Subobject.ofLE (B ⊓ N) N inf_le_right) ≅
          cokernel (image.preComp
            (HomologicalComplex.homologyMap (K.filtration.diagram.map
              (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) n)
            (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n))),
        C.arrow ≫ K.X.iCycles n = a ≫ N.arrow ∧
        C.arrow ≫ K.X.homologyπ n =
          b ≫ image.ι (HomologicalComplex.homologyMap
            (K.filtration.ι.app (op p)) n) ∧
        a ≫ cokernel.π (Subobject.ofLE (B ⊓ N) N inf_le_right) ≫ e.hom =
          b ≫ cokernel.π (image.preComp
            (HomologicalComplex.homologyMap (K.filtration.diagram.map
              (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) n)
            (HomologicalComplex.homologyMap
              (K.filtration.ι.app (op p)) n))) := by
  have hbounded : ∀ n : ℤ,
      {p : ℤ | ¬ IsZero ((E.page 1 (by omega)).X (p, n - p))}.Finite := by
    intro n
    obtain ⟨a, b, hab⟩ := isIso_homologyMap_filtration_map_outside_interval K hzero hiso n
    refine Set.Finite.subset (Set.finite_Ico a b) fun p hp => ?_
    by_contra hmem
    have hout : p < a ∨ b ≤ p := by
      simpa only [Set.mem_Ico, not_and_or, not_le, not_lt] using hmem
    obtain ⟨h₀, h₁⟩ := hab p hout
    apply hp
    apply Filtered.isZero_page K Z D E hE 1 p (n - p) n (by omega) (by omega)
    rw [hZ 1 p n, hD 1 p n, show (1 : ℤ) - 1 = 0 by omega,
      show p - (1 : ℤ) + 1 = p by omega,
      Z_eq_F K F hF Z hZ (le_refl 0) (p + 1) n,
      Z_eq_F K F hF Z hZ (le_refl 0) p (n - 1)]
    exact CochainComplex.firstPage_cycles_le_boundaries K F hF p n inferInstance inferInstance
  have hfinite : ∀ n : ℤ, ∃ a b : ℤ, a ≤ b ∧ FH n a = ⊤ ∧ FH n b = ⊥ :=
    fun n => inducedFiltration_isFinite K FH hFH n (hzero n) (hiso n)
  have hstable : ∀ p n : ℤ,
      IsGLB (Set.range fun r : ℕ ↦
          F p n ⊓ (Subobject.pullback (K.X.d n (n + 1))).obj (F (p + r) (n + 1)) ⊔
            F (p + 1) n)
        (kernelSubobject (K.X.d n (n + 1)) ⊓ F p n ⊔ F (p + 1) n) ∧
      IsLUB (Set.range fun r : ℕ ↦
          F p n ⊓ (Subobject.«exists» (K.X.d (n - 1) n)).obj (F (p - r) (n - 1)) ⊔
            F (p + 1) n)
        (imageSubobject (K.X.d (n - 1) n) ⊓ F p n ⊔ F (p + 1) n) := by
    intro p n
    exact ⟨CochainComplex.isGLB_stableCycles_of_eventually_isZero K F hF p n (hzero (n + 1)),
      CochainComplex.isLUB_stableBoundaries_of_eventually_isIso K F hF p n (hiso n)⟩
  exact ⟨hbounded, hfinite,
    differential_eq_zero_of_finite_diagonal E 1 (by omega) hbounded,
    hstable, fun p n => exists_iso_of_stable_cycles_boundaries K F hF p n (hstable p n)⟩

open FilteredComplexSpectralSequence Subobject in
/-- **The spectral sequence of a filtered complex.**  For a filtered complex `(K^•, F)` of an
abelian category, with `Z_r^{p, q} = F^p K^n ⊓ (d^n)⁻¹(F^{p + r}K^{n + 1})` and
`D_r^{p, q} = Z_{r - 1}^{p + 1, q - 1} ⊔ d^{n - 1}(Z_{r - 1}^{p - r + 1, q + r - 2})` as
subobjects of `K^n`, the quotients `E_r^{p, q} = Z_r^{p, q} / (D_r^{p, q} ⊓ Z_r^{p, q})` are the
pages of a cohomological spectral sequence whose differential is induced by `d`, whose zeroth
page is `gr^p K^•`, and whose first page is therefore `H^n(gr^p K^•)`. -/
@[stacks 012M]
public theorem exists_cohomologicalSpectralSequence
    {A : Type u} [Category.{v} A] [Abelian A]
    (K : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ)
    (F : ∀ (_p n : ℤ), Subobject (K.X.X n))
    (hF : ∀ p n : ℤ, F p n = Subobject.mk ((K.filtration.ι.app (op p)).f n))
    (Z : ∀ (_r _p n : ℤ), Subobject (K.X.X n))
    (hZ : ∀ r p n : ℤ, Z r p n =
      F p n ⊓ (Subobject.pullback (K.X.d n (n + 1))).obj (F (p + r) (n + 1)))
    (D : ∀ (_r _p n : ℤ), Subobject (K.X.X n))
    (hD : ∀ r p n : ℤ, D r p n = Z (r - 1) (p + 1) n ⊔
      (Subobject.«exists» (K.X.d (n - 1) n)).obj (Z (r - 1) (p - r + 1) (n - 1))) :
    ∃ (E : CohomologicalSpectralSequence A 0)
      (e : ∀ (r p q n : ℤ) (hr : 0 ≤ r) (_ : n = p + q), (E.page r hr).X (p, q) ≅
        cokernel (Subobject.ofLE _ _ (inf_le_right : D r p n ⊓ Z r p n ≤ Z r p n)))
      (α : ∀ (p q n : ℤ), n = p + q → ((E.page 0 le_rfl).X (p, q) ≅
        ((FilteredObject.gr p).obj K).X n)),
      (∀ (r p q n : ℤ) (hr : 0 ≤ r) (hn : n = p + q),
        ∃ δ : (Z r p n : A) ⟶ (Z r (p + r) (n + 1) : A),
          δ ≫ (Z r (p + r) (n + 1)).arrow = (Z r p n).arrow ≫ K.X.d n (n + 1) ∧
          cokernel.π (Subobject.ofLE _ _ (inf_le_right : D r p n ⊓ Z r p n ≤ Z r p n)) ≫
              (e r p q n hr hn).inv ≫ (E.page r hr).d (p, q) (p + r, q - r + 1) =
            δ ≫ cokernel.π (Subobject.ofLE _ _ (inf_le_right :
                D r (p + r) (n + 1) ⊓ Z r (p + r) (n + 1) ≤ Z r (p + r) (n + 1))) ≫
              (e r (p + r) (q - r + 1) (n + 1) hr (by omega)).inv) ∧
      (∀ (p q n : ℤ) (hn : n = p + q) (u : (Z 0 p n : A) ⟶ (K.filtration.obj (op p)).X n),
        u ≫ (K.filtration.ι.app (op p)).f n = (Z 0 p n).arrow →
        cokernel.π (Subobject.ofLE _ _ (inf_le_right : D 0 p n ⊓ Z 0 p n ≤ Z 0 p n)) ≫
            (e 0 p q n le_rfl hn).inv ≫ (α p q n hn).hom =
          u ≫ (FilteredObject.grMapπ (FilteredObject.succHom p) K).f n) ∧
      (∀ (p q n : ℤ) (hn : n = p + q),
        (E.page 0 le_rfl).d (p, q) (p, q + 1) ≫ (α p (q + 1) (n + 1) (by omega)).hom =
          (α p q n hn).hom ≫
            ((FilteredObject.gr p).obj K).d n (n + 1)) ∧
      (∀ p q n : ℤ, n = p + q → Nonempty ((E.page 1).X (p, q) ≅
        ((FilteredObject.gr p).obj K).homology n)) := by
  obtain ⟨rfl, rfl⟩ := eq_cycles_and_boundaries K F Z hZ D hD
  have hanti : ∀ p p' n : ℤ, p ≤ p' → F p' n ≤ F p n := fun _ _ n hp => F_antitone K F hF hp n
  obtain ⟨α, h2, h3, h4⟩ := exists_iso_gradedPiece_zeroPage K F hF hanti
  refine ⟨spectralSequence K.X F hanti, eIso K.X F hanti, α, ?_, h2, h3, h4⟩
  intro r p q n hr hn
  refine ⟨deltaCycles K.X F r p n, deltaCycles_arrow K.X F r p n, ?_⟩
  subst hn
  rw [spectralSequence_d, eIso_inv_rfl, Category.id_comp, ← Category.assoc, π_comp_pageMap,
    Category.assoc]

open FilteredComplexSpectralSequence Subobject in
/-- **The page turn of the spectral sequence of a filtered complex, on classes.**  Let `E` be the
spectral sequence of a filtered complex `(K^•, F)`, presented as in
`exists_cohomologicalSpectralSequence` by its pages `E_r^{p, q} = Z_r^{p,q}/D_r^{p,q}` and its
differentials induced by `d`. Then for `r ≥ 0` and `r' = r + 1` the cohomology of `(E_r, d_r)` at
`(p, q)` is `E_{r'}^{p, q}`, by an isomorphism sending the class of an `r`-cycle represented by
`x ∈ Z_{r'}^{p, q} ⊆ Z_r^{p, q}` to the class of `x` in `E_{r'}^{p, q}`. -/
public theorem exists_iso_homology_page_of_mem_cycles
    {A : Type u} [Category.{v} A] [Abelian A]
    (K : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ)
    (F : ∀ (_p n : ℤ), Subobject (K.X.X n))
    (hF : ∀ p n : ℤ, F p n = Subobject.mk ((K.filtration.ι.app (op p)).f n))
    (Z : ∀ (_r _p n : ℤ), Subobject (K.X.X n))
    (hZ : ∀ r p n : ℤ, Z r p n =
      F p n ⊓ (Subobject.pullback (K.X.d n (n + 1))).obj (F (p + r) (n + 1)))
    (D : ∀ (_r _p n : ℤ), Subobject (K.X.X n))
    (hD : ∀ r p n : ℤ, D r p n = Z (r - 1) (p + 1) n ⊔
      (Subobject.«exists» (K.X.d (n - 1) n)).obj (Z (r - 1) (p - r + 1) (n - 1)))
    (E : CohomologicalSpectralSequence A 0)
    (e : ∀ (r p q n : ℤ) (hr : 0 ≤ r) (_ : n = p + q), (E.page r hr).X (p, q) ≅
      cokernel (Subobject.ofLE _ _ (inf_le_right : D r p n ⊓ Z r p n ≤ Z r p n)))
    (hδ : ∀ (r p q n : ℤ) (hr : 0 ≤ r) (hn : n = p + q),
      ∃ δ : (Z r p n : A) ⟶ (Z r (p + r) (n + 1) : A),
        δ ≫ (Z r (p + r) (n + 1)).arrow = (Z r p n).arrow ≫ K.X.d n (n + 1) ∧
        cokernel.π (Subobject.ofLE _ _ (inf_le_right : D r p n ⊓ Z r p n ≤ Z r p n)) ≫
            (e r p q n hr hn).inv ≫ (E.page r hr).d (p, q) (p + r, q - r + 1) =
          δ ≫ cokernel.π (Subobject.ofLE _ _ (inf_le_right :
              D r (p + r) (n + 1) ⊓ Z r (p + r) (n + 1) ≤ Z r (p + r) (n + 1))) ≫
            (e r (p + r) (q - r + 1) (n + 1) hr (by omega)).inv)
    (r r' p q n : ℤ) (hr : 0 ≤ r) (hr' : r' = r + 1) (hn : n = p + q) :
    ∃ ψ : (E.page r hr).homology (p, q) ≅ (E.page r' (by omega)).X (p, q),
      ∀ {T : A} (y : T ⟶ (E.page r hr).cycles (p, q)) (x : T ⟶ (Z r' p n : A))
        (x' : T ⟶ (Z r p n : A)), x' ≫ (Z r p n).arrow = x ≫ (Z r' p n).arrow →
        y ≫ (E.page r hr).iCycles (p, q) = x' ≫
          cokernel.π (Subobject.ofLE _ _ (inf_le_right : D r p n ⊓ Z r p n ≤ Z r p n)) ≫
            (e r p q n hr hn).inv →
        y ≫ (E.page r hr).homologyπ (p, q) ≫ ψ.hom = x ≫
          cokernel.π (Subobject.ofLE _ _
            (inf_le_right : D r' p n ⊓ Z r' p n ≤ Z r' p n)) ≫
            (e r' p q n (by omega) hn).inv := by
  obtain ⟨rfl, rfl⟩ := eq_cycles_and_boundaries K F Z hZ D hD
  subst hn hr'
  have hanti : ∀ p p' n : ℤ, p ≤ p' → F p' n ≤ F p n := fun _ _ n hp => F_antitone K F hF hp n
  -- the differential of `E_r`, read through `e`, is the model differential
  have key : ∀ (a b n m : ℤ) (hn : n = a + b) (hm : m = n + 1),
      (e r a b n hr hn).hom ≫ pageMap' K.X F r a n (a + r) m rfl hm =
        (E.page r hr).d (a, b) (a + r, b - r + 1) ≫
          (e r (a + r) (b - r + 1) m hr (by omega)).hom := by
    intro a b n m hn hm
    subst hn hm
    obtain ⟨δ, hδ₁, hδ₂⟩ := hδ r a b (a + b) hr rfl
    have hδ₃ : δ = deltaCycles' K.X F r a (a + b) (a + r) (a + b + 1) rfl rfl := by
      rw [← cancel_mono (FilteredComplexSpectralSequence.cycles K.X F r (a + r) (a + b + 1)).arrow,
          hδ₁,
        deltaCycles'_arrow]
    rw [← cancel_epi (e r a b (a + b) hr rfl).inv,
      ← cancel_epi (cokernel.π (den K.X F r a (a + b))), Iso.inv_hom_id_assoc,
      π_comp_pageMap', reassoc_of% hδ₂, hδ₃, Iso.inv_hom_id, Category.comp_id]
  have hcomm : ∀ (i j : ℤ × ℤ), (ComplexShape.up' ((r, 1 - r) : ℤ × ℤ)).Rel i j →
      (e r i.1 i.2 (i.1 + i.2) hr rfl).hom ≫ (pageComplex K.X F r).d i j =
        (E.page r hr).d i j ≫ (e r j.1 j.2 (j.1 + j.2) hr rfl).hom := by
    rintro ⟨a, b⟩ j hij
    rw [ComplexShape.up'_Rel] at hij
    obtain rfl : j = (a + r, b - r + 1) := by
      rw [← hij]
      exact Prod.ext (Prod.fst_add _ _) (by rw [Prod.snd_add]; ring)
    rw [pageComplex_d K.X F r hij]
    exact key a b (a + b) ((a + r) + (b - r + 1)) rfl (by ring)
  let Φ : E.page r hr ≅ pageComplex K.X F r := HomologicalComplex.Hom.isoOfComponents
    (fun i : ℤ × ℤ => e r i.1 i.2 (i.1 + i.2) hr rfl) hcomm
  refine ⟨HomologicalComplex.homologyMapIso Φ (p, q) ≪≫ pageHomologyIso K.X F hanti r (p, q) ≪≫
    (e (r + 1) p q (p + q) (by omega) rfl).symm, fun {T} y x x' hx hy => ?_⟩
  have hy' : (y ≫ HomologicalComplex.cyclesMap Φ.hom (p, q)) ≫
      (pageComplex K.X F r).iCycles (p, q) = x' ≫ cokernel.π (den K.X F r p (p + q)) := by
    rw [Category.assoc, HomologicalComplex.cyclesMap_i, reassoc_of% hy]
    simp [Φ]
  have h := homologyπ_comp_pageHomologyIso_hom K.X F hanti r (p, q) _ x x' hx hy'
  rw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, HomologicalComplex.homologyMapIso_hom,
    HomologicalComplex.homologyπ_naturality_assoc, reassoc_of% h]


end CochainComplex

end
