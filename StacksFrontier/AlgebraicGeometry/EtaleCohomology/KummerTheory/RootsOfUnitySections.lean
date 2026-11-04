module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.FirstCohomologyOfRootsOfUnity

/-!
# Sections of the sheaf of `n`-th roots of unity

Let `C` be a site and `F : C ⥤ Scheme` a functor whose presheaf of units is a sheaf. The sheaf
of `n`-th roots of unity `μ_n` is by definition the kernel of the `n`-th power map on the sheaf
of units `𝐆_m`. This file describes its sections concretely: over an object `T` of the site they
are exactly the units of the ring of global functions on `F T` whose `n`-th power is one, the
correspondence being given by the inclusion `μ_n ⟶ 𝐆_m`.

## Main definitions

* `AlgebraicGeometry.rootSection` is the section of `μ_n` attached to a global unit whose
  `n`-th power is one.

## Main results

* `AlgebraicGeometry.rootsOfUnityι_rootSection`: the inclusion `μ_n ⟶ 𝐆_m` carries
  `AlgebraicGeometry.rootSection` to the corresponding section of the sheaf of units. This
  characterizes it.
* `AlgebraicGeometry.exists_rootSection`: every section of `μ_n` is one of these.
* `AlgebraicGeometry.pow_eq_one_rootUnit`: the global unit underlying a section of `μ_n` has
  `n`-th power one.
* `AlgebraicGeometry.rootSection_injective`, `AlgebraicGeometry.rootSection_mul` and
  `AlgebraicGeometry.rootSection_restrict`: the correspondence is injective, carries products of
  units to sums of sections, and is compatible with restriction along a morphism of the site.

## Implementation notes

Kernels of abelian sheaves are computed section by section: the inclusion of sheaves into
presheaves preserves limits and so does evaluation at an object of the site, so the composite
carries the kernel defining `μ_n` to the kernel of the `n`-th power map on the sections of the
sheaf of units, which `AddCommGrpCat.kernelIsoKer` identifies with a group-theoretic kernel.
That kernel consists of the sections killed by `n`, which in multiplicative notation are the
units whose `n`-th power is one.

A section of `μ_n` is therefore obtained by inverting an isomorphism rather than by a formula, so
`AlgebraicGeometry.rootSection` is defined by choice and is characterized by
`AlgebraicGeometry.rootsOfUnityι_rootSection`.

The analogue of this description for Mathlib's small étale site, where sections carry an extra
universe lift, is `Stacks.Kummer.rootsOfUnitySection_bijective`.

## References

* [Stacks Project, Tag 040N](https://stacks.math.columbia.edu/tag/040N)
* [Stacks Project, Tag 03P4](https://stacks.math.columbia.edu/tag/03P4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

universe v u

variable {C : Type v} [Category.{u} C] (J : GrothendieckTopology C) (F : C ⥤ Scheme.{u})
  (h : Presheaf.IsSheaf J (unitsPresheaf F)) (n : ℕ)

/-- The section of the sheaf of units attached to a global unit determines that unit. -/
private theorem unitsSection_injective (T : C) {a b : (Scheme.Γ.obj (op (F.obj T)))ˣ}
    (hab : unitsSection F T a = unitsSection F T b) : a = b :=
  Additive.ofMul.injective hab

/-- A global unit whose section of the sheaf of units is killed by `n` has `n`-th power one. -/
private theorem pow_eq_one_of_nsmul_unitsSection (T : C) (a : (Scheme.Γ.obj (op (F.obj T)))ˣ)
    (ha : n • unitsSection F T a = 0) : a ^ n = 1 :=
  Additive.ofMul.injective ha

/-- The section of the sheaf of units attached to a global unit whose `n`-th power is one is
killed by `n`. -/
theorem nsmul_unitsSection_eq_zero (T : C) (a : (Scheme.Γ.obj (op (F.obj T)))ˣ) (ha : a ^ n = 1) :
    n • unitsSection F T a = 0 :=
  congrArg Additive.ofMul ha

/-- The section of the sheaf of units attached to a product of global units is the sum of the
sections attached to the factors. -/
theorem unitsSection_mul (T : C) (a b : (Scheme.Γ.obj (op (F.obj T)))ˣ) :
    unitsSection F T (a * b) = unitsSection F T a + unitsSection F T b :=
  ofMul_mul a b

/-- Restricting the section of the sheaf of units given by a global unit pulls that unit back
along the corresponding morphism of schemes. -/
theorem unitsSection_restrict {T T' : C} (f : T' ⟶ T) (a : (Scheme.Γ.obj (op (F.obj T)))ˣ) :
    (unitsPresheaf F).map f.op (unitsSection F T a) =
      unitsSection F T' (Units.map (Scheme.Γ.map (F.map f).op).hom.toMonoidHom a) :=
  rfl

/-- **The sheaf of `n`-th roots of unity is computed section by section.** Over an object of the
site, the inclusion into the sheaf of units kills `n`-th multiples, is injective, and has for
its image the sections killed by `n`. -/
private theorem kernelι_app_spec (T : C) :
    (∀ z, n • ((kernel.ι (powerSheaf J F h n)).hom.app (op T) z) = 0) ∧
      Function.Injective ((kernel.ι (powerSheaf J F h n)).hom.app (op T)) ∧
        ∀ y, n • y = 0 → ∃ x, (kernel.ι (powerSheaf J F h n)).hom.app (op T) x = y := by
  let E : Sheaf J AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
    sheafToPresheaf J AddCommGrpCat.{u} ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op T)
  let G := unitsSheaf J F h
  let p := powerSheaf J F h n
  let : PreservesLimit (parallelPair p 0) E := inferInstance
  have hp : E.map p = n • 𝟙 (E.obj G) := by
    apply AddCommGrpCat.hom_ext
    ext x
    rfl
  let e := (PreservesKernel.iso E p).trans <|
    (kernelIsoOfEq hp).trans (AddCommGrpCat.kernelIsoKer (n • 𝟙 (E.obj G)))
  have he : e.hom ≫ AddCommGrpCat.ofHom
      (AddSubgroup.subtype (n • 𝟙 (E.obj G)).hom.ker) = (kernel.ι p).hom.app (op T) := by
    dsimp [e]
    simp only [Category.assoc]
    rw [AddCommGrpCat.kernelIsoKer_hom_comp_subtype, kernelIsoOfEq_hom_comp_ι,
      PreservesKernel.iso_hom]
    simpa [E] using kernelComparison_comp_ι p E
  have hval : ∀ z, ((e.hom z).1 : _) = (kernel.ι p).hom.app (op T) z := fun z =>
    ConcreteCategory.congr_hom he z
  have hbij := ConcreteCategory.bijective_of_isIso e.hom
  refine ⟨fun z => ?_, fun x y hxy => hbij.1 (Subtype.ext ?_), fun y hy => ?_⟩
  · exact (congrArg (fun w => (n • 𝟙 (E.obj G)).hom w) (hval z)).symm.trans
      (AddMonoidHom.mem_ker.mp (e.hom z).2)
  · exact (hval x).trans (hxy.trans (hval y).symm)
  · obtain ⟨x, hx⟩ := hbij.2 ⟨y, AddMonoidHom.mem_ker.mpr hy⟩
    exact ⟨x, (hval x).symm.trans (congrArg Subtype.val hx)⟩

/-- **A section of the sheaf of units killed by `n` comes from the sheaf of `n`-th roots of
unity.** -/
theorem exists_rootsOfUnityι_app (T : C) (y : (unitsPresheaf F).obj (op T)) (hy : n • y = 0) :
    ∃ x : (rootsOfUnitySheaf J F h n).obj.obj (op T),
      (kernel.ι (powerSheaf J F h n)).hom.app (op T) x = y :=
  (kernelι_app_spec J F h n T).2.2 y hy

/-- A global unit whose `n`-th power is one, as a section of the sheaf of `n`-th roots of
unity. -/
def rootSection (T : C) (a : (Scheme.Γ.obj (op (F.obj T)))ˣ) (ha : a ^ n = 1) :
    (rootsOfUnitySheaf J F h n).obj.obj (op T) :=
  (exists_rootsOfUnityι_app J F h n T (unitsSection F T a)
    (nsmul_unitsSection_eq_zero F n T a ha)).choose

/-- The inclusion of the roots of unity into the units carries
`AlgebraicGeometry.rootSection` to the corresponding section of the sheaf of units. -/
theorem rootsOfUnityι_rootSection (T : C) (a : (Scheme.Γ.obj (op (F.obj T)))ˣ) (ha : a ^ n = 1) :
    (kernel.ι (powerSheaf J F h n)).hom.app (op T) (rootSection J F h n T a ha) =
      unitsSection F T a :=
  (exists_rootsOfUnityι_app J F h n T (unitsSection F T a)
    (nsmul_unitsSection_eq_zero F n T a ha)).choose_spec

/-- A section of the sheaf of `n`-th roots of unity whose image in the sheaf of units is the
section of a global unit is the `AlgebraicGeometry.rootSection` of that unit. -/
private theorem eq_rootSection_of_unitsSection (T : C) {a : (Scheme.Γ.obj (op (F.obj T)))ˣ}
    (ha : a ^ n = 1) {x : (rootsOfUnitySheaf J F h n).obj.obj (op T)}
    (hx : (kernel.ι (powerSheaf J F h n)).hom.app (op T) x = unitsSection F T a) :
    x = rootSection J F h n T a ha :=
  (kernelι_app_spec J F h n T).2.1
    (hx.trans (rootsOfUnityι_rootSection J F h n T a ha).symm)

/-- A section of the sheaf of `n`-th roots of unity has `n`-th power one as a unit. -/
theorem pow_eq_one_rootUnit (T : C) (x : (rootsOfUnitySheaf J F h n).obj.obj (op T)) :
    (Additive.toMul ((kernel.ι (powerSheaf J F h n)).hom.app (op T) x) :
        (Scheme.Γ.obj (op (F.obj T)))ˣ) ^ n = 1 :=
  pow_eq_one_of_nsmul_unitsSection F n T
    (Additive.toMul ((kernel.ι (powerSheaf J F h n)).hom.app (op T) x))
    ((kernelι_app_spec J F h n T).1 x)

/-- **Every section of the sheaf of `n`-th roots of unity is one of these.** -/
theorem exists_rootSection (T : C) (x : (rootsOfUnitySheaf J F h n).obj.obj (op T)) :
    ∃ (a : (Scheme.Γ.obj (op (F.obj T)))ˣ) (ha : a ^ n = 1), x = rootSection J F h n T a ha :=
  ⟨Additive.toMul ((kernel.ι (powerSheaf J F h n)).hom.app (op T) x),
    pow_eq_one_rootUnit J F h n T x,
    eq_rootSection_of_unitsSection J F h n T (pow_eq_one_rootUnit J F h n T x) rfl⟩

/-- `AlgebraicGeometry.rootSection` is injective in the unit. -/
theorem rootSection_injective (T : C) {a b : (Scheme.Γ.obj (op (F.obj T)))ˣ} (ha : a ^ n = 1)
    (hb : b ^ n = 1) (hab : rootSection J F h n T a ha = rootSection J F h n T b hb) : a = b :=
  unitsSection_injective F T
    ((rootsOfUnityι_rootSection J F h n T a ha).symm.trans
      ((congrArg (fun z => (kernel.ι (powerSheaf J F h n)).hom.app (op T) z) hab).trans
        (rootsOfUnityι_rootSection J F h n T b hb)))

/-- `AlgebraicGeometry.rootSection` is a homomorphism: the product of units goes to the sum of
sections. -/
theorem rootSection_mul (T : C) (a b : (Scheme.Γ.obj (op (F.obj T)))ˣ) (ha : a ^ n = 1)
    (hb : b ^ n = 1) :
    rootSection J F h n T (a * b) (by rw [mul_pow, ha, hb, one_mul]) =
      rootSection J F h n T a ha + rootSection J F h n T b hb :=
  (eq_rootSection_of_unitsSection J F h n T _ <|
    ((((kernel.ι (powerSheaf J F h n)).hom.app (op T)).hom.map_add
        (rootSection J F h n T a ha) (rootSection J F h n T b hb)).trans
      (congrArg₂ (· + ·) (rootsOfUnityι_rootSection J F h n T a ha)
        (rootsOfUnityι_rootSection J F h n T b hb))).trans
    (unitsSection_mul F T a b).symm).symm

/-- `AlgebraicGeometry.rootSection` is compatible with restriction: restricting the section
corresponds to pulling the unit back. -/
theorem rootSection_restrict {T T' : C} (f : T' ⟶ T) (a : (Scheme.Γ.obj (op (F.obj T)))ˣ)
    (ha : a ^ n = 1) :
    (rootsOfUnitySheaf J F h n).obj.map f.op (rootSection J F h n T a ha) =
      rootSection J F h n T' (Units.map (Scheme.Γ.map (F.map f).op).hom.toMonoidHom a)
        (by rw [← map_pow, ha, map_one]) :=
  eq_rootSection_of_unitsSection J F h n T' _
    ((NatTrans.naturality_apply (kernel.ι (powerSheaf J F h n)).hom f.op
        (rootSection J F h n T a ha)).trans
      ((congrArg (fun z => (unitsPresheaf F).map f.op z)
          (rootsOfUnityι_rootSection J F h n T a ha)).trans
        (unitsSection_restrict F f a)))

end AlgebraicGeometry

end
