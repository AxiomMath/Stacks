module

public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.HomogeneousTwistRaising
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.HomogeneousTwistTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SubmoduleFactorThru
public import StacksFrontier.AlgebraicGeometry.QcohRestrictEquiv.IsoLocality
import StacksCore.Tactic.StacksAttribute

/-!
# The degree-`n` forms of `L^⋆` are the degree-zero forms twisted by `L^{⊗ n}`

Let `f : X ⟶ S` be a morphism of schemes, `L` an invertible `𝒪_X`-module and `L^⋆ ⟶ X` the
complement of the zero section of the associated line bundle. Multiplication of a relative form on
`L^⋆` by the homogeneous function of a local section of `L^{⊗ n}` carries the degree-`m` part
`Ω^p_{L^⋆/S, m}` of the pushed-forward relative forms *isomorphically* onto the degree-`(n + m)`
part. At `m = 0` that is the identification of clause (1) of Tag 0FUH,

`Ω^p_{L^⋆/S, n} = Ω^p_{L^⋆/S, 0} ⊗_{𝒪_X} L^{⊗ n}`,

for every integer `n`, on an arbitrary scheme over `S` and for an arbitrary invertible module.

## Main definitions

* `Stacks.LineBundle.Situation.gradedAt`: the degree-`k` part, as a sheaf of modules read at the
  indexing the tensor product of Tag 05NA is defined over.
* `Stacks.LineBundle.Situation.gradedTwistComparison`: **the comparison map
  `Ω^p_{L^⋆/S, m} ⊗_{𝒪_X} L^{⊗ n} ⟶ Ω^p_{L^⋆/S, n + m}`**, the corestriction of
  `Situation.twistHom` to the two graded pieces.
* `Stacks.LineBundle.Situation.gradedTwistIso`: **the identification of clause (1) of Tag
  0FUH.**

## Main results

* `Stacks.LineBundle.Situation.laurentSmul_one`: multiplying a form by the constant function `1`
  leaves it alone.
* `Stacks.LineBundle.Situation.laurentSmul_genInt_injective` and
  `Situation.exists_laurentSmul_genInt`: **over a trivializing open, multiplication by the
  homogeneous function of the degree-`n` generator is injective, and carries `Ω^p_{L^⋆/S, m}`
  onto `Ω^p_{L^⋆/S, n + m}`.**
* `Stacks.LineBundle.Situation.gradedTwistHom_mem_sieve`: the comparison lands in the
  degree-`(n + m)` part, locally and hence everywhere.
* `Stacks.LineBundle.Situation.isIso_gradedTwistComparison`: **the comparison map is an
  isomorphism.**

## Implementation notes

The local half rests on one datum, the invertible pair of homogeneous functions
`Stacks.LineBundle.Situation.laurentFunctionOfOpen_genInt_mul` of a trivializing open: injectivity
is multiplication by the inverse function, and surjectivity produces the preimage as
multiplication by that same inverse function, whose membership in the degree-`m` part is
`Situation.laurentSmul_mem_gradedLaurentForms` — the degree bookkeeping over an arbitrary open.
Neither half needs `Situation.isHomogeneousLaurentForm_of_smul_genInt`: that converse is stated
for a *homogeneous form* over an affine open, while what is wanted here is a statement about an
arbitrary section of a graded piece over an arbitrary trivializing open, and the degree
bookkeeping of
`StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.HomogeneousTwistRaising` already supplies it in
that generality.

The corestriction is `SheafOfModules.Submodule.factorThru` against the `isSheaf` field of the
target graded piece, so the containment only has to be checked locally. That is what makes it
cheap: over a trivializing open the *surjectivity* half of
`TwistGenerator.bijective_tensorSectionsAt_genInt` writes an arbitrary section of the sheafified
tensor product as the section determined by a section of the degree-`m` part together with the
degree-`n` generator, and no general statement about sections of a sheafification is needed.

The same bijection is what reduces invertibility to the two halves above: a section of the source
over a trivializing open is `Stacks.SheafOfModules.tensorSectionsAt` of a section of the
degree-`m` part with the generator, and the map sends it to the product of that section with the
generator's homogeneous function. Invertibility is then local on `X` by
`Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_coversTop`, over the cover
`Situation.exists_affine_trivializing_cover_over_affine`; `L` is still trivial over each open
inside a member of that cover, by `Stacks.SheafOfModules.isoUnitOverOfHom`, so the requirement of
that criterion is met at every object carrying a morphism to a member.

## Clause (1) and its tag

What is proved here is the identification of clause (1) as an isomorphism of sheaves of
`𝒪_X`-modules, for every `p : ℕ` and every `n : ℤ`. The printed clause asserts it *as
quasi-coherent `𝒪_X`-modules*, and the quasi-coherence of the two sides is
`Stacks.LineBundle.Situation.isQuasicoherent_gradedAt` and
`Situation.isQuasicoherent_gradedTwistSource` of
`StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.HomogeneousTwistCompatible`. The global
`@[stacks 0FUH]` attribute for clause (1) is carried by those two together with
`Situation.gradedTwistIso` here; the three affine `@[stacks 0FUH]` attributes of
`StacksFrontier/RingTheory/DeRham/WeightComparison.lean` are the affine local cases of all three
clauses and stay where they are. Clauses (2) and (3) are proved globally by
`Stacks.LineBundle.Situation.deRhamComplexIsoTotalWeightZero` of
`StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TotalSpaceWeightZero` and
`Stacks.LineBundle.Situation.gradedFormsIsoLaurent` of
`StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TotalSpaceLaurentComparison`.

*Where the quasi-coherence comes from.* `Situation.isQuasicoherent_laurentFormsPushforward` gives
quasi-coherence of the whole pushforward, but a `SheafOfModules.Submodule` of a quasi-coherent
module is not quasi-coherent in general, so `Situation.gradedLaurentForms` inherits nothing from
it. What discharges it is
`Stacks.AlgebraicGeometry.GabberColimit.isQuasicoherent_sheafSubmodule`
(`StacksFrontier/AlgebraicGeometry/CardinalGeneratedColimit/Basic.lean:275`), applied to the family
of `Γ(X, U)`-spans of the homogeneous forms of degree `n` over the affine opens `U` of `X`. Its
hypothesis is `GabberColimit.IsCompatible`: for nested affine opens `W ≤ U` the span over `W` is
the span of the restrictions from `U`. The restriction half is
`Situation.isHomogeneousLaurentForm_map` with no bridging; the other half is the recursion of
`StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.HomogeneousTwistCompatible`, which takes a
homogeneous form over `π⁻¹W` apart with quasi-coherence of `L^{⊗ j}`, the Leibniz rule and the
naturality of the graded multiplication. That recursion does not close on its own: the Leibniz
rule leaves the differential of a function pulled back from `W`, which is again a degree-zero
one-form over `π⁻¹W`. What breaks that circularity from outside is
`Situation.laurentDifferential_pullback_mem_span` of
`StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.LaurentPullbackDifferential`.

The route through Tag 0GQM and `Situation.isIso_gradedTwistComparison` — quasi-coherence in
degree zero transported to every other degree along the comparison — is *not* what is used: the
recursion runs for every `n` at once, so every degree is obtained directly. Tag 0GQM is still
used, but only for the tensor product `Ω^p_{L^⋆/S, 0} ⊗_{𝒪_X} L^{⊗ n}` itself.

## References

* [Stacks Project, Tag 0FUH](https://stacks.math.columbia.edu/tag/0FUH), clause (1)
* [Stacks Project, Tag 0FU9](https://stacks.math.columbia.edu/tag/0FU9), the graded pieces
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA), the tensor product of
  sheaves of modules
-/
@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.TwistGenerator
open Stacks.SheafOfModules.TensorSheafification (structureSheaf)
open Stacks.SheafOfModules.Tensor (sheafTensor)

universe u

namespace Stacks.LineBundle

variable (D : Situation.{u})

/-- **Multiplying a form by the constant function `1` leaves it alone.** The `MulAction`
instance lives at the `D.laurentFormsAlgebra.piece p` indexing of the forms, so `one_smul` does
not apply to the pushforward spelling and the form is moved by `id (α := ·)`, as in
`Situation.laurentSmul` itself. -/
theorem Situation.laurentSmul_one (p : ℤ) (U : D.X.Opens)
    (ω : (D.laurentFormsPushforward p).val.obj (op U)) :
    D.laurentSmul p U 1 ω = ω :=
  one_smul (D.laurentSpectrum.sheaf.obj.obj (op (D.laurentSpectrumToBase ⁻¹ᵁ U)))
    (id (α := (D.laurentFormsAlgebra.piece p).val.obj
      (op (D.laurentSpectrumToBase ⁻¹ᵁ U))) ω)

/-- Multiplying a form by `f` and then by an inverse `g` of `f` leaves it alone. -/
private theorem Situation.laurentSmul_laurentSmul_of_mul_eq_one (p : ℤ) (U : D.X.Opens)
    {g f : D.laurentSpectrum.sheaf.obj.obj (op (D.laurentSpectrumToBase ⁻¹ᵁ U))} (h : g * f = 1)
    (ω : (D.laurentFormsPushforward p).val.obj (op U)) :
    D.laurentSmul p U g (D.laurentSmul p U f ω) = ω :=
  (D.laurentSmul_mul p U g f ω).symm.trans
    ((congrArg (fun g => D.laurentSmul p U g ω) h).trans (D.laurentSmul_one p U ω))

/-- Membership in a graded piece transported along an equation between the degrees. -/
private theorem Situation.mem_gradedLaurentForms_of_degree_eq (p : ℕ) {k l : ℤ} (h : k = l)
    {V : (Opens D.X)ᵒᵖ} {ω : (D.laurentFormsPushforward (p : ℤ)).val.obj V}
    (hω : ω ∈ (D.gradedLaurentForms p k).obj V) :
    ω ∈ (D.gradedLaurentForms p l).obj V :=
  Eq.mpr (congrArg (fun j => ω ∈ (D.gradedLaurentForms p j).obj V) h.symm) hω

variable {W : D.X.Opens}
  (e : D.L.over W ≅ SheafOfModules.unit (D.X.ringCatSheaf.over W))

/-- **The homogeneous functions of the generator family in degrees `n` and `-n` multiply to
`1`**, the ring of functions on the inverse image of the trivializing open being commutative. -/
theorem Situation.laurentFunctionOfOpen_genInt_mul_neg (n : ℤ) :
    D.laurentFunctionOfOpen n W (genInt D.L e n) *
        D.laurentFunctionOfOpen (-n) W (genInt D.L e (-n)) = 1 :=
  (mul_comm (D.laurentFunctionOfOpen n W (genInt D.L e n))
      (D.laurentFunctionOfOpen (-n) W (genInt D.L e (-n)))).trans
    (D.laurentFunctionOfOpen_genInt_mul e n)

/-- **Multiplication by the homogeneous function of the degree-`n` generator is injective** on
sections of the pushed-forward forms over a trivializing open: multiplication by the homogeneous
function of the degree-`(-n)` generator undoes it. -/
theorem Situation.laurentSmul_genInt_injective (p : ℤ) (n : ℤ) :
    Function.Injective fun ω : (D.laurentFormsPushforward p).val.obj (op W) =>
      D.laurentSmul p W (D.laurentFunctionOfOpen n W (genInt D.L e n)) ω := by
  intro ω η h
  have key : ∀ ξ : (D.laurentFormsPushforward p).val.obj (op W),
      D.laurentSmul p W (D.laurentFunctionOfOpen (-n) W (genInt D.L e (-n)))
          (D.laurentSmul p W (D.laurentFunctionOfOpen n W (genInt D.L e n)) ξ) = ξ :=
    fun ξ => D.laurentSmul_laurentSmul_of_mul_eq_one p W (D.laurentFunctionOfOpen_genInt_mul e n) ξ
  exact ((key ω).symm.trans (congrArg
    (D.laurentSmul p W (D.laurentFunctionOfOpen (-n) W (genInt D.L e (-n)))) h)).trans (key η)

/-- **Every section of `Ω^p_{L^⋆/S, n + m}` over a trivializing open is the product of a section
of `Ω^p_{L^⋆/S, m}` with the homogeneous function of the degree-`n` generator.** The preimage is
the product with the homogeneous function of the degree-`(-n)` generator, which lies in the
degree-`m` part by the degree bookkeeping `Situation.laurentSmul_mem_gradedLaurentForms`, the two
functions multiplying to `1`. -/
theorem Situation.exists_laurentSmul_genInt {p : ℕ} (m n : ℤ)
    {η : (D.laurentFormsPushforward (p : ℤ)).val.obj (op W)}
    (hη : η ∈ (D.gradedLaurentForms p (n + m)).obj (op W)) :
    ∃ ω ∈ (D.gradedLaurentForms p m).obj (op W),
      D.laurentSmul (p : ℤ) W (D.laurentFunctionOfOpen n W (genInt D.L e n)) ω = η := by
  refine ⟨D.laurentSmul (p : ℤ) W (D.laurentFunctionOfOpen (-n) W (genInt D.L e (-n))) η,
    D.mem_gradedLaurentForms_of_degree_eq p (show -n + (n + m) = m by omega)
      (D.laurentSmul_mem_gradedLaurentForms (-n) (genInt D.L e (-n)) hη), ?_⟩
  exact D.laurentSmul_laurentSmul_of_mul_eq_one (p : ℤ) W
    (D.laurentFunctionOfOpen_genInt_mul_neg e n) η

/-- **The twist map on the section of the tensor product determined by a pair of sections**: it
is multiplication of the form by the homogeneous function of the section of `L^{⊗ n}`. -/
theorem Situation.twistHom_val_app_tensorSectionsAt (p n : ℤ) (U : (Opens D.X)ᵒᵖ)
    (ω : (D.pushforwardAt p).val.obj U) (x : (D.tensorPowerAt n).val.obj U) :
    (D.twistHom p n).val.app U
        (Stacks.SheafOfModules.tensorSectionsAt D.X.sheaf.obj D.X.ringCatSheaf.property U
          (D.pushforwardAt p) (D.tensorPowerAt n) ω x) =
      D.laurentSmul p U.unop (D.laurentFunctionOfOpen n U.unop x) ω :=
  D.twistHom_toSheafify_tmul p n U ω x

/-! ### The comparison map of clause (1) -/

/-- The degree-`k` part of the pushed-forward forms, as a sub-`𝒪_X`-module of the pushforward read
at the indexing the tensor product of Tag 05NA is defined over. The two indexings are equal by
`rfl` and `id` is what moves a term between them, as for `Situation.pushforwardAt`. -/
def Situation.gradedSubmoduleAt (p : ℕ) (k : ℤ) : (D.pushforwardAt (p : ℤ)).Submodule :=
  id (α := (D.pushforwardAt (p : ℤ)).Submodule) (D.gradedLaurentForms p k)

/-- The degree-`k` part `Ω^p_{L^⋆/S, k}` as a sheaf of modules at that indexing: the subsheaf of
the pushed-forward forms it cuts out. -/
def Situation.gradedAt (p : ℕ) (k : ℤ) :
    _root_.SheafOfModules.{u} (structureSheaf D.X.sheaf.obj D.X.ringCatSheaf.property) :=
  (D.gradedSubmoduleAt p k).toSheafOfModules

/-- **The comparison map of clause (1) of Tag 0FUH, before corestriction**: multiplication by the
homogeneous functions of the local sections of `L^{⊗ n}`, restricted to the degree-`m` part of the
pushed-forward forms. -/
def Situation.gradedTwistHom (p : ℕ) (m n : ℤ) :
    ((sheafTensor D.X.sheaf).obj (D.gradedAt p m)).obj (D.tensorPowerAt n) ⟶
      D.pushforwardAt (p : ℤ) :=
  Stacks.AlgebraicGeometry.GradedAlgebraTwist.tensorMap D.X.sheaf.obj
      D.X.ringCatSheaf.property (D.gradedSubmoduleAt p m).ι (𝟙 (D.tensorPowerAt n)) ≫
    D.twistHom (p : ℤ) n

/-- **The comparison map on the section of the tensor product determined by a pair of sections**:
it is multiplication of the form by the homogeneous function of the section of `L^{⊗ n}`. -/
theorem Situation.gradedTwistHom_tensorSectionsAt (p : ℕ) (m n : ℤ) (U : (Opens D.X)ᵒᵖ)
    (y : (D.gradedAt p m).val.obj U) (x : (D.tensorPowerAt n).val.obj U) :
    (D.gradedTwistHom p m n).val.app U
        (Stacks.SheafOfModules.tensorSectionsAt D.X.sheaf.obj D.X.ringCatSheaf.property U
          (D.gradedAt p m) (D.tensorPowerAt n) y x) =
      D.laurentSmul (p : ℤ) U.unop (D.laurentFunctionOfOpen n U.unop x)
        ((D.gradedSubmoduleAt p m).ι.val.app U y) :=
  (congrArg ((D.twistHom (p : ℤ) n).val.app U)
      (Stacks.AlgebraicGeometry.GradedAlgebraTwist.tensorMap_app D.X.sheaf.obj
        D.X.ringCatSheaf.property (D.gradedSubmoduleAt p m).ι (𝟙 (D.tensorPowerAt n))
        U y x)).trans
    (D.twistHom_val_app_tensorSectionsAt (p : ℤ) n U _ _)

/-- **Every point of an open of `X` has a neighbourhood inside it over which `L` is trivial**: an
affine trivializing neighbourhood of the point, cut down by the open. -/
theorem Situation.exists_trivializing_le (U : D.X.Opens) {z : D.X} (hz : z ∈ U) :
    ∃ (W : D.X.Opens) (_ : W ≤ U), z ∈ W ∧
      Nonempty (D.L.over W ≅ SheafOfModules.unit (D.X.ringCatSheaf.over W)) := by
  obtain ⟨U₀, -, hzU₀, -, hL⟩ := D.exists_trivializing_affineOpen_over_affine z
  exact ⟨U₀.1 ⊓ U, inf_le_right, ⟨hzU₀, hz⟩,
    ⟨Stacks.SheafOfModules.isoUnitOverOfHom D.L (homOfLE inf_le_left) hL.some⟩⟩

/-- **The comparison map lands in the degree-`(n + m)` part.** Locally on `X` every section of its
source is the section determined by a section of the degree-`m` part together with the degree-`n`
generator — that is the surjectivity half of
`TwistGenerator.bijective_tensorSectionsAt_genInt` — and on such a section the map is
multiplication by the homogeneous function of that generator, which raises the degree by `n` by
`Situation.laurentSmul_mem_gradedLaurentForms`. -/
theorem Situation.gradedTwistHom_mem_sieve (p : ℕ) (m n : ℤ) (X : (Opens D.X)ᵒᵖ)
    (t : (((sheafTensor D.X.sheaf).obj (D.gradedAt p m)).obj (D.tensorPowerAt n)).val.obj X) :
    (D.gradedSubmoduleAt p (n + m)).toSubmodule.toSubfunctor.sieveOfSection
        ((D.gradedTwistHom p m n).val.app X t) ∈
      Opens.grothendieckTopology (D.X : TopCat) X.unop := by
  rw [Opens.mem_grothendieckTopology]
  intro z hz
  obtain ⟨W, hWX, hzW, ⟨eW⟩⟩ := D.exists_trivializing_le X.unop hz
  refine ⟨W, homOfLE hWX, ?_, hzW⟩
  obtain ⟨y, hy⟩ := (bijective_tensorSectionsAt_genInt D.L eW n (D.gradedAt p m)).2
    ((((sheafTensor D.X.sheaf).obj (D.gradedAt p m)).obj
      (D.tensorPowerAt n)).val.map (homOfLE hWX).op t)
  refine D.mem_gradedLaurentForms_of_eq p (n + m)
    ((PresheafOfModules.naturality_apply (D.gradedTwistHom p m n).val
          (homOfLE hWX).op t).symm.trans
      ((congrArg ((D.gradedTwistHom p m n).val.app (op W)) hy.symm).trans
        (D.gradedTwistHom_tensorSectionsAt p m n (op W) y (genInt D.L eW n)))) ?_
  exact D.laurentSmul_mem_gradedLaurentForms n (genInt D.L eW n)
    y.2

/-- **The comparison map of clause (1) of Tag 0FUH**: multiplication by the homogeneous functions
of the local sections of `L^{⊗ n}`, as a map
`Ω^p_{L^⋆/S, m} ⊗_{𝒪_X} L^{⊗ n} ⟶ Ω^p_{L^⋆/S, n + m}` of sheaves of `𝒪_X`-modules. Its
corestriction to the degree-`(n + m)` part is `Situation.gradedTwistHom_mem_sieve`, membership in
a graded piece being local. -/
def Situation.gradedTwistComparison (p : ℕ) (m n : ℤ) :
    ((sheafTensor D.X.sheaf).obj (D.gradedAt p m)).obj (D.tensorPowerAt n) ⟶
      D.gradedAt p (n + m) :=
  (D.gradedSubmoduleAt p (n + m)).factorThru (D.gradedTwistHom p m n)
    fun X t => (D.gradedSubmoduleAt p (n + m)).isSheaf _
      (D.gradedTwistHom_mem_sieve p m n X t)

/-- **The comparison map, followed by the inclusion of the degree-`(n + m)` part, is
multiplication by the homogeneous functions.** -/
theorem Situation.gradedTwistComparison_ι (p : ℕ) (m n : ℤ) :
    D.gradedTwistComparison p m n ≫ (D.gradedSubmoduleAt p (n + m)).ι =
      D.gradedTwistHom p m n :=
  (D.gradedSubmoduleAt p (n + m)).factorThru_ι (D.gradedTwistHom p m n) _


/-! ### The comparison is an isomorphism -/

/-- The comparison map on sections, read through the subtype cutting out the degree-`(n + m)`
part: it is multiplication by the homogeneous functions. -/
theorem Situation.gradedTwistComparison_val (p : ℕ) (m n : ℤ) (U : (Opens D.X)ᵒᵖ)
    (t : (((sheafTensor D.X.sheaf).obj (D.gradedAt p m)).obj (D.tensorPowerAt n)).val.obj U) :
    ((D.gradedTwistComparison p m n).val.app U t).val =
      (D.gradedTwistHom p m n).val.app U t :=
  rfl

/-- **Over an open of `X` trivializing `L` the comparison map is bijective on sections.** The
sections of its source over such an open are the sections of the degree-`m` part tensored with the
degree-`n` generator, by `TwistGenerator.bijective_tensorSectionsAt_genInt`, and on those the map
is multiplication by the generator's homogeneous function, which is injective by
`Situation.laurentSmul_genInt_injective` and onto the degree-`(n + m)` part by
`Situation.exists_laurentSmul_genInt`. -/
theorem Situation.bijective_gradedTwistComparison_app (p : ℕ) (m n : ℤ) {W : D.X.Opens}
    (e : D.L.over W ≅ SheafOfModules.unit (D.X.ringCatSheaf.over W)) :
    Function.Bijective ((D.gradedTwistComparison p m n).val.app (op W)) := by
  have hτ := bijective_tensorSectionsAt_genInt D.L e n (D.gradedAt p m)
  have hval : ∀ y : (D.gradedAt p m).val.obj (op W),
      ((D.gradedTwistComparison p m n).val.app (op W)
          (Stacks.SheafOfModules.tensorSectionsAt D.X.sheaf.obj D.X.ringCatSheaf.property
            (op W) (D.gradedAt p m) (D.tensorPowerAt n) y (genInt D.L e n))).val =
        D.laurentSmul (p : ℤ) W (D.laurentFunctionOfOpen n W (genInt D.L e n)) y.val :=
    fun y => (D.gradedTwistComparison_val p m n (op W) _).trans
      (D.gradedTwistHom_tensorSectionsAt p m n (op W) y (genInt D.L e n))
  refine ⟨fun t₁ t₂ h => ?_, fun η => ?_⟩
  · obtain ⟨y₁, rfl⟩ := hτ.2 t₁
    obtain ⟨y₂, rfl⟩ := hτ.2 t₂
    exact congrArg (fun y : (D.gradedAt p m).val.obj (op W) =>
        Stacks.SheafOfModules.tensorSectionsAt D.X.sheaf.obj D.X.ringCatSheaf.property
          (op W) (D.gradedAt p m) (D.tensorPowerAt n) y (genInt D.L e n))
      (Subtype.ext (D.laurentSmul_genInt_injective e (p : ℤ) n
        (((hval y₁).symm.trans (congrArg Subtype.val h)).trans (hval y₂))))
  · obtain ⟨ω, hω, hωη⟩ := D.exists_laurentSmul_genInt e m n η.2
    exact ⟨Stacks.SheafOfModules.tensorSectionsAt D.X.sheaf.obj D.X.ringCatSheaf.property
        (op W) (D.gradedAt p m) (D.tensorPowerAt n) ⟨ω, hω⟩ (genInt D.L e n),
      Subtype.ext ((hval ⟨ω, hω⟩).trans hωη)⟩

/-- **The comparison map is an isomorphism**:
`Ω^p_{L^⋆/S, m} ⊗_{𝒪_X} L^{⊗ n} ≅ Ω^p_{L^⋆/S, n + m}`. Invertibility is local on `X` by
`Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_coversTop`, and the affine opens
trivializing `L` and mapping into an affine open of `S` cover `X` by
`Situation.exists_affine_trivializing_cover_over_affine`; over each open inside one of them `L` is
still trivial, by `Stacks.SheafOfModules.isoUnitOverOfHom`. -/
theorem Situation.isIso_gradedTwistComparison (p : ℕ) (m n : ℤ) :
    IsIso (D.gradedTwistComparison p m n) := by
  obtain ⟨I, U, V, hcov, -, htriv⟩ := D.exists_affine_trivializing_cover_over_affine
  refine Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_coversTop
    ((Opens.coversTop_iff (D.X : TopCat) fun i => (U i).1).mpr
      (TopologicalSpace.IsOpenCover.mk hcov)) _ fun i W hW => ?_
  rw [ConcreteCategory.isIso_iff_bijective]
  exact D.bijective_gradedTwistComparison_app p m n
    (Stacks.SheafOfModules.isoUnitOverOfHom D.L hW (htriv i).some)

/-- **Clause (1) of Tag 0FUH**: the degree-`n` part of the pushed-forward relative differential
forms of the complement of the zero section is the degree-zero part twisted by `L^{⊗ n}`,
`Ω^p_{L^⋆/S, n} = Ω^p_{L^⋆/S, 0} ⊗_{𝒪_X} L^{⊗ n}`. The isomorphism is multiplication of a form by
the homogeneous function of a local section of `L^{⊗ n}`, so it is the canonical map and not a
choice. That the two sides are *quasi-coherent* `𝒪_X`-modules, which is the rest of what the
printed clause asserts, is `Stacks.LineBundle.Situation.isQuasicoherent_gradedAt` and
`Situation.isQuasicoherent_gradedTwistSource` of
`StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.HomogeneousTwistCompatible`. -/
@[stacks 0FUH "clause (1): the degree-n part is identified with the twisted degree-zero part"]
def Situation.gradedTwistIso (p : ℕ) (n : ℤ) :
    ((sheafTensor D.X.sheaf).obj (D.gradedAt p 0)).obj (D.tensorPowerAt n) ≅
      D.gradedAt p n :=
  have := D.isIso_gradedTwistComparison p 0 n
  asIso (D.gradedTwistComparison p 0 n) ≪≫ eqToIso (congrArg (D.gradedAt p) (add_zero n))

end Stacks.LineBundle

end
