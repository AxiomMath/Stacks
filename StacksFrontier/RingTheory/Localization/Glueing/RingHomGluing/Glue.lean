module

public import StacksFrontier.RingTheory.Localization.Glueing.RingHomGluing.Away
public import StacksFrontier.RingTheory.Localization.Glueing.Transport
import all StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingEquivalence

/-!
# The glueing datum of finitely many maximal ideals

Let `A` be a commutative ring, let `m i` be finitely many pairwise distinct maximal ideals with
intersection `I = ⨅ j, m j`, and let `x : Fin r → A` generate `I`.  Let `f i : A_{m i} → B i` be
ring maps whose kernels and cokernels are killed by a power of the maximal ideal, and let `T` be
a model of `∏ i, B i` as an algebra over `A' = ∏ i, A_{m i}`.

The map `A' → T` becomes bijective after inverting any element of `I`, because its kernel and its
cokernel are `I A'`-power torsion.  So the canonical system of glueing data of `A` for the family
`x` can be transported along it: this file builds the resulting system, whose generic part is `T`
and whose local pieces are the localizations of `A`, and identifies the base change of its module
of compatible sections.  Together with the formal glueing equivalence of Stacks 05ER this says
that the module of compatible sections becomes `T` over the product of the localizations — the
module-theoretic content of Stacks 0EAE.

## Main results

* `Stacks.RingHomGluing.bijective_transportMap` — the structure map `A' → T` is bijective after
  inverting a generator of the intersection.
* `Stacks.RingHomGluing.glueDatum` — the system of glueing data with generic part `T`.
* `Stacks.RingHomGluing.exists_baseChange_equiv_glueTarget` — the base change of the compatible
  sections to `A'` is `T`, by way of the projection to the generic component.

## References

* [Stacks Project, Tag 05ER](https://stacks.math.columbia.edu/tag/05ER)
* [Stacks Project, Tag 0EAE](https://stacks.math.columbia.edu/tag/0EAE)
-/

@[expose] public noncomputable section

universe u v w t

namespace Stacks.RingHomGluing

open CategoryTheory Cech TensorProduct FormalGlueing

section Construction

variable {A : Type u} [CommRing A] {I : Type w} [Finite I] (m : I → Ideal A)
  [∀ i, (m i).IsMaximal] {B : I → Type v} [∀ i, CommRing (B i)]
  {T : Type max u v w} [CommRing T] [Algebra (∀ i, Localization.AtPrime (m i)) T]
  {r : ℕ} (x : Fin r → A)

/-! ### The canonical datum of the base ring, and the structure map -/

/-- The ring `A` as a module over itself, lifted to a larger universe. -/
abbrev liftedBase (A : Type u) [CommRing A] : ModuleCat.{max u t} A :=
  ModuleCat.of A (ULift.{t} A)

/-- The canonical glueing datum of `A` for the family `x`. -/
abbrev baseDatum : ModuleGlueingDatum.{u, max u w, v}
    (∀ i, Localization.AtPrime (m i)) x (localizationComparisons x) :=
  canonicalDatum.{u, max u w, v} (∀ i, Localization.AtPrime (m i)) x
    (liftedBase.{u, max v w} A)

/-- The glued target as an object of the category of `A'`-modules. -/
abbrev glueTarget : ModuleCat.{max u v w} (∀ i, Localization.AtPrime (m i)) :=
  ModuleCat.of (∀ i, Localization.AtPrime (m i)) T

omit [Finite I] in
/-- The canonical identification of the generic part of the canonical datum of `A` with the
product of the localizations. -/
def glueRid : TensorProduct A (∀ i, Localization.AtPrime (m i)) (ULift.{max v w} A) ≃ₗ[
      ∀ i, Localization.AtPrime (m i)] (∀ i, Localization.AtPrime (m i)) :=
  (AlgebraTensorModule.congr (LinearEquiv.refl (∀ i, Localization.AtPrime (m i))
      (∀ i, Localization.AtPrime (m i))) (ULift.moduleEquiv (R := A) (M := A))).trans
    (AlgebraTensorModule.rid A (∀ i, Localization.AtPrime (m i))
      (∀ i, Localization.AtPrime (m i)))

omit [Finite I] in
/-- The identification of the generic part, on a pure tensor. -/
@[simp] theorem glueRid_tmul (s : ∀ i, Localization.AtPrime (m i)) (z : ULift.{max v w} A) :
    glueRid.{u, v, w} m (s ⊗ₜ[A] z) = z.down • s := by
  simp [glueRid]

/-- The structure map of the glued target, as a map out of the generic part of the canonical
datum of `A`. -/
def gluePsi : (baseDatum.{u, v, w} m x).generic ⟶ glueTarget.{u, v, w} m (T := T) :=
  ModuleCat.ofHom ((gluedLinearMap m T).comp (glueRid.{u, v, w} m).toLinearMap)

omit [Finite I] in
/-- The structure map, evaluated. -/
theorem gluePsi_apply (z : TensorProduct A (∀ i, Localization.AtPrime (m i))
    (ULift.{max v w} A)) :
    (gluePsi.{u, v, w} m x (T := T)).hom z =
      algebraMap (∀ i, Localization.AtPrime (m i)) T (glueRid.{u, v, w} m z) := rfl

/-! ### Bijectivity after inverting a generator -/

variable {f : ∀ i, Localization.AtPrime (m i) →+* B i} (ev : ∀ i, T →+* B i)

omit [Finite I] in
/-- The range of the structure map is the range of the map from the product of the
localizations. -/
theorem range_gluePsi :
    LinearMap.range (gluePsi.{u, v, w} m x (T := T)).hom =
      LinearMap.range (gluedLinearMap m T) := by
  refine le_antisymm (fun s hs ↦ ?_) (fun s hs ↦ ?_)
  · obtain ⟨z, rfl⟩ := hs
    exact ⟨glueRid.{u, v, w} m z, (gluePsi_apply m x z).symm⟩
  · obtain ⟨c, rfl⟩ := hs
    refine ⟨(glueRid.{u, v, w} m).symm c, ?_⟩
    rw [gluePsi_apply, LinearEquiv.apply_symm_apply]
    rfl

/-- The kernel of the structure map is `I A'`-power torsion. -/
theorem isIPowerTorsion_ker_gluePsi (hm : Pairwise fun i j ↦ m i ≠ m j)
    (hev : ∀ (a : ∀ i, Localization.AtPrime (m i)) (i : I),
      ev i (algebraMap (∀ i, Localization.AtPrime (m i)) T a) = f i (a i))
    (hker : ∀ i, KernelIsKilledByIdealPower (f i)
      ((m i).map (algebraMap A (Localization.AtPrime (m i))))) :
    IsIPowerTorsion (∀ i, Localization.AtPrime (m i))
      (LinearMap.ker (gluePsi.{u, v, w} m x (T := T)).hom)
      ((⨅ j, m j).map (algebraMap A (∀ i, Localization.AtPrime (m i)))) := by
  intro z
  have hz : gluedLinearMap m T (glueRid.{u, v, w} m z.1) = 0 :=
    (gluePsi_apply.{u, v, w} m x z.1).symm.trans (LinearMap.mem_ker.1 z.2)
  obtain ⟨n, hn, hz'⟩ := isIPowerTorsion_ker m ev hm hev hker ⟨glueRid.{u, v, w} m z.1, hz⟩
  refine ⟨n, hn, fun a ha ↦ ?_⟩
  have h1 : a • glueRid.{u, v, w} m z.1 = 0 := congrArg Subtype.val (hz' a ha)
  have key : a • z.1 = 0 := (glueRid.{u, v, w} m).injective
    ((map_smul (glueRid.{u, v, w} m) a z.1).trans (h1.trans (map_zero _).symm))
  exact Subtype.ext key

/-- The cokernel of the structure map is `I A'`-power torsion. -/
theorem isIPowerTorsion_cokernel_gluePsi (hm : Pairwise fun i j ↦ m i ≠ m j)
    (hev : ∀ (a : ∀ i, Localization.AtPrime (m i)) (i : I),
      ev i (algebraMap (∀ i, Localization.AtPrime (m i)) T a) = f i (a i))
    (hinj : ∀ s s' : T, (∀ i, ev i s = ev i s') → s = s')
    (hcoker : ∀ i, CokernelIsKilledByIdealPower (f i)
      ((m i).map (algebraMap A (Localization.AtPrime (m i))))) :
    IsIPowerTorsion (∀ i, Localization.AtPrime (m i))
      (T ⧸ LinearMap.range (gluePsi.{u, v, w} m x (T := T)).hom)
      ((⨅ j, m j).map (algebraMap A (∀ i, Localization.AtPrime (m i)))) := by
  rw [range_gluePsi]
  exact isIPowerTorsion_cokernel m ev hm hev hinj hcoker

/-- **The glued target agrees with the product of the localizations away from the maximal
ideals.** The structure map becomes bijective after inverting any generator of the
intersection. -/
theorem bijective_transportMap (hx : Ideal.span (Set.range x) = ⨅ j, m j)
    (hm : Pairwise fun i j ↦ m i ≠ m j)
    (hev : ∀ (a : ∀ i, Localization.AtPrime (m i)) (i : I),
      ev i (algebraMap (∀ i, Localization.AtPrime (m i)) T a) = f i (a i))
    (hinj : ∀ s s' : T, (∀ i, ev i s = ev i s') → s = s')
    (hker : ∀ i, KernelIsKilledByIdealPower (f i)
      ((m i).map (algebraMap A (Localization.AtPrime (m i)))))
    (hcoker : ∀ i, CokernelIsKilledByIdealPower (f i)
      ((m i).map (algebraMap A (Localization.AtPrime (m i))))) (i : Fin r) :
    Function.Bijective (transportMap (∀ i, Localization.AtPrime (m i)) x
      (baseDatum.{u, v, w} m x) (glueTarget.{u, v, w} m (T := T))
      (gluePsi.{u, v, w} m x) i) := by
  have hmem : algebraMap A (∀ i, Localization.AtPrime (m i)) (x i) ∈
      (⨅ j, m j).map (algebraMap A (∀ i, Localization.AtPrime (m i))) :=
    Ideal.mem_map_of_mem _ (hx ▸ Ideal.subset_span (Set.mem_range_self i))
  exact FormalGlueing.localizedMap_bijective
    ((⨅ j, m j).map (algebraMap A (∀ i, Localization.AtPrime (m i))))
    (gluePsi.{u, v, w} m x).hom
    (isIPowerTorsion_ker_gluePsi m x ev hm hev hker)
    (isIPowerTorsion_cokernel_gluePsi m x ev hm hev hinj hcoker) _ hmem

/-! ### The glued datum and its compatible sections -/

variable (hψ : ∀ i, Function.Bijective (transportMap (∀ i, Localization.AtPrime (m i)) x
  (baseDatum.{u, v, w} m x) (glueTarget.{u, v, w} m (T := T)) (gluePsi.{u, v, w} m x) i))

/-- The system of glueing data whose generic part is the glued target and whose local pieces are
those of `A` itself. -/
abbrev glueDatum : ModuleGlueingDatum.{u, max u w, v}
    (∀ i, Localization.AtPrime (m i)) x (localizationComparisons x) :=
  transportDatum (∀ i, Localization.AtPrime (m i)) x (baseDatum.{u, v, w} m x)
    (glueTarget.{u, v, w} m (T := T)) (gluePsi.{u, v, w} m x) hψ

/-- The module of compatible sections of the glued datum: the underlying module of the glued
ring. -/
abbrev glueSections :=
  compatibleSections (∀ i, Localization.AtPrime (m i)) x (localizationComparisons x)
    (glueDatum.{u, v, w} m x hψ)

/-- **The glued module.** The base change to the product of the localizations of the module of
compatible sections is the glued target, by way of the projection to the generic component. -/
theorem exists_baseChange_equiv_glueTarget (hx : Ideal.span (Set.range x) = ⨅ j, m j)
    (hm : Pairwise fun i j ↦ m i ≠ m j) :
    ∃ e : TensorProduct A (∀ i, Localization.AtPrime (m i))
        (glueSections.{u, v, w} m x hψ) ≃ₗ[∀ i, Localization.AtPrime (m i)] T,
      ∀ (s : ∀ i, Localization.AtPrime (m i)) (y : glueSections.{u, v, w} m x hψ),
        e (s ⊗ₜ[A] y) = s • (y.1.1 : T) := by
  have hflat : Module.Flat A (∀ i, Localization.AtPrime (m i)) :=
    flat_pi_localizationAtPrime m
  have hq : Function.Bijective (Ideal.quotientMap
      ((Ideal.span (Set.range x)).map (algebraMap A (∀ i, Localization.AtPrime (m i))))
      (algebraMap A (∀ i, Localization.AtPrime (m i))) Ideal.le_comap_map) := by
    rw [hx]
    exact quotientMap_bijective m hm
  exact ⟨LinearEquiv.ofBijective
    (FormalGlueing.sectionsGenericCounit _ x (glueDatum.{u, v, w} m x hψ))
    ⟨FormalGlueing.genericCounit_injective _ x hflat hq _,
      FormalGlueing.genericCounit_surjective _ x hflat hq _⟩, fun s y ↦ rfl⟩

end Construction

end Stacks.RingHomGluing

end
