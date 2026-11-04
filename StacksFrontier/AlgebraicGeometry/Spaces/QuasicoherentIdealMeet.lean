module

public import StacksFrontier.AlgebraicGeometry.Spaces.CartesianRelations
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealOrderIso
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisorSumEffective
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentFiniteProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentStructureSheaf

/-!
# The meet of two quasi-coherent submodules is quasi-coherent

Let `M` be a sheaf of modules on a site and let `N₁, N₂ ⊆ M` be two sheaves of submodules.
Their meet `N₁ ⊓ N₂`, which is formed section by section, is the fibre product of the two
inclusions:

```
            N₁ ⊓ N₂ ⟶ N₁
               ↓        ↓
              N₂   ⟶   M
```

That square is cartesian for an entirely elementary reason — a section of `M` lying both in
`N₁` and in `N₂` lies in `N₁ ⊓ N₂`, and the inclusion of `N₁ ⊓ N₂` is injective, so the
factorisation is unique — and it holds over any site and any sheaf of rings.

On the small étale site of an algebraic space `F` this turns the meet into a *limit* of
quasi-coherent modules: a fibre product in an abelian category is the kernel of a map out of a
biproduct, a biproduct of quasi-coherent modules is quasi-coherent, and being cartesian on
affine charts is stable under kernels.  Hence `N₁ ⊓ N₂` is quasi-coherent as soon as `N₁`, `N₂`
and the ambient `M` are.  Taking `M = 𝒪_F` gives the statement for sheaves of ideals, where the
ambient hypothesis is automatic: the structure sheaf is quasi-coherent.

## Main definitions

* `Stacks.SheafOfModules.submoduleInfFst` and `Stacks.SheafOfModules.submoduleInfSnd` are the
  two projections `N₁ ⊓ N₂ ⟶ N₁` and `N₁ ⊓ N₂ ⟶ N₂`.
* `Stacks.SheafOfModules.submoduleInfLift` factors a morphism which factors through both `N₁`
  and `N₂` through their meet.
* `AlgebraicGeometry.Space.quasicoherentIdealsInf` is the meet of two quasi-coherent sheaves of
  ideals of `𝒪_X`, as an element of `AlgebraicGeometry.Space.QuasicoherentIdeals`, and
  `AlgebraicGeometry.Space.quasicoherentIdealsMin` installs it as the `⊓` of that type.

## Main results

* `Stacks.SheafOfModules.isPullback_submoduleInf`: **the meet of two sheaves of submodules is
  the fibre product of their inclusions.**
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isPullback`: a fibre product of
  quasi-coherent `𝒪_F`-modules is quasi-coherent.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_inf`: **the meet of two quasi-coherent sheaves
  of submodules of a quasi-coherent `𝒪_F`-module is quasi-coherent.**
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_idealInf`: **the meet of two quasi-coherent
  sheaves of ideals of `𝒪_X` is quasi-coherent**, with no hypothesis beyond quasi-coherence of
  the two.

## Implementation notes

Everything about the meet itself is proved at the level of an arbitrary site, where the meet of
two sheaves of submodules is Mathlib's `SheafOfModules.Submodule` lattice operation, computed
section by section.  The two projections are
`PresheafOfModules.Submodule.homOfLE` applied to `inf_le_left` and `inf_le_right`, and the lift
out of a competing cone is `Stacks.PresheafOfModules.Submodule.factor`, the corestriction of a
morphism of presheaves of modules to a submodule containing its local images.  Uniqueness of
the lift is monomorphy of the inclusion of `N₁ ⊓ N₂`.

Quasi-coherence of the fibre product follows the argument of
`AlgebraicGeometry.Space.isQuasicoherentOnSite_intersectionPushforward`: a fibre product in an
abelian category is the kernel of the map `G₁ ⊞ G₂ ⟶ G` induced by the two arrows with one of
them negated, which is Mathlib's
`CategoryTheory.Abelian.PullbackToBiproductIsKernel.isLimitPullbackToBiproduct`; being cartesian
on affine charts is stable under kernels by
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isLimit`, a biproduct of quasi-coherent
modules is quasi-coherent by `SheafOfModules.isQuasicoherentOnSite_biprod`, and Descent,
Proposition 03DX(2) converts between quasi-coherence and the cartesian condition in both
directions.  Here the statement is phrased for an arbitrary cartesian square rather than for
Mathlib's chosen `CategoryTheory.Limits.pullback`, so that the meet — which is *not* that chosen
fibre product — can be fed to it directly; the comparison is
`CategoryTheory.IsPullback.isoPullback`.

Nothing is assumed.  The module universe is the universe `u` of the schemes, which is where the
category of `𝒪_F`-modules is abelian and hence has the fibre product.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.SheafOfModules

universe u v w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  {M : _root_.SheafOfModules.{w} R}

/-- The projection of the meet of two sheaves of submodules onto the first one. -/
def submoduleInfFst (N₁ N₂ : M.Submodule) :
    (N₁ ⊓ N₂).toSheafOfModules ⟶ N₁.toSheafOfModules :=
  ⟨_root_.PresheafOfModules.Submodule.homOfLE
    (le_of_eq_of_le (_root_.SheafOfModules.Submodule.toSubmodule_inf N₁ N₂) inf_le_left)⟩

/-- The projection of the meet of two sheaves of submodules onto the second one. -/
def submoduleInfSnd (N₁ N₂ : M.Submodule) :
    (N₁ ⊓ N₂).toSheafOfModules ⟶ N₂.toSheafOfModules :=
  ⟨_root_.PresheafOfModules.Submodule.homOfLE
    (le_of_eq_of_le (_root_.SheafOfModules.Submodule.toSubmodule_inf N₁ N₂) inf_le_right)⟩

/-- The first projection of the meet, followed by the inclusion of `N₁`, is the inclusion of the
meet. -/
@[reassoc]
theorem submoduleInfFst_ι (N₁ N₂ : M.Submodule) :
    submoduleInfFst N₁ N₂ ≫ N₁.ι = (N₁ ⊓ N₂).ι := rfl

/-- The second projection of the meet, followed by the inclusion of `N₂`, is the inclusion of
the meet. -/
@[reassoc]
theorem submoduleInfSnd_ι (N₁ N₂ : M.Submodule) :
    submoduleInfSnd N₁ N₂ ≫ N₂.ι = (N₁ ⊓ N₂).ι := rfl

/-- **A morphism into `M` which factors through both `N₁` and `N₂` factors through their
meet.**  The two factorisations are asked to agree as morphisms into `M`, which is what makes
each local section of the source land in both submodules. -/
def submoduleInfLift (N₁ N₂ : M.Submodule) {Z : _root_.SheafOfModules.{w} R}
    (a : Z ⟶ N₁.toSheafOfModules) (b : Z ⟶ N₂.toSheafOfModules)
    (hab : a ≫ N₁.ι = b ≫ N₂.ι) : Z ⟶ (N₁ ⊓ N₂).toSheafOfModules :=
  ⟨_root_.Stacks.PresheafOfModules.Submodule.factor (N₁ ⊓ N₂).toSubmodule (a ≫ N₁.ι).val
    (fun U x => by
      change ((a ≫ N₁.ι).val.app U) x ∈ N₁.obj U ⊓ N₂.obj U
      refine Submodule.mem_inf.mpr ⟨(a.val.app U x).2, ?_⟩
      rw [congrArg (fun φ : Z ⟶ M => (φ.val.app U) x) hab]
      exact (b.val.app U x).2)⟩

/-- The lift into the meet recovers the given factorisation after the inclusion of the meet. -/
theorem submoduleInfLift_ι (N₁ N₂ : M.Submodule) {Z : _root_.SheafOfModules.{w} R}
    (a : Z ⟶ N₁.toSheafOfModules) (b : Z ⟶ N₂.toSheafOfModules)
    (hab : a ≫ N₁.ι = b ≫ N₂.ι) :
    submoduleInfLift N₁ N₂ a b hab ≫ (N₁ ⊓ N₂).ι = a ≫ N₁.ι := rfl

/-- **The meet of two sheaves of submodules is the fibre product of their inclusions.**

Existence of the factorisation through the meet is
`Stacks.SheafOfModules.submoduleInfLift` and its uniqueness is monomorphy of the inclusion of
the meet. -/
theorem isPullback_submoduleInf (N₁ N₂ : M.Submodule) :
    IsPullback (submoduleInfFst N₁ N₂) (submoduleInfSnd N₁ N₂) N₁.ι N₂.ι := by
  have hw : submoduleInfFst N₁ N₂ ≫ N₁.ι = submoduleInfSnd N₁ N₂ ≫ N₂.ι := by
    rw [submoduleInfFst_ι, submoduleInfSnd_ι]
  refine IsPullback.of_isLimit' ⟨hw⟩ (PullbackCone.IsLimit.mk hw
    (fun s => submoduleInfLift N₁ N₂ s.fst s.snd s.condition) (fun s => ?_) (fun s => ?_)
    (fun s m h₁ h₂ => ?_))
  · exact (cancel_mono N₁.ι).1 rfl
  · exact (cancel_mono N₂.ι).1 s.condition
  · refine (cancel_mono (N₁ ⊓ N₂).ι).1 ?_
    rw [submoduleInfLift_ι, ← submoduleInfFst_ι, ← Category.assoc, h₁]

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **A fibre product of quasi-coherent `𝒪_F`-modules is quasi-coherent.**

The fibre product is the kernel of the map `G₁ ⊞ G₂ ⟶ G` induced by the two arrows of the
cospan with one of them negated; a binary biproduct of quasi-coherent modules is quasi-coherent,
being cartesian on affine charts is stable under kernels, and Descent, Proposition 03DX(2)
converts between the two conditions in both directions.

The hypothesis is an arbitrary cartesian square rather than Mathlib's chosen fibre product, so
that a module presented as a fibre product in some other way — such as a meet of submodules —
can be fed to it without first being identified with that chosen one. -/
theorem isQuasicoherentOnSite_of_isPullback {P G₁ G₂ G : Modules.{u, u} B S hS F hF}
    {p₁ : P ⟶ G₁} {p₂ : P ⟶ G₂} {f : G₁ ⟶ G} {g : G₂ ⟶ G} (h : IsPullback p₁ p₂ f g)
    (h₁ : G₁.IsQuasicoherentOnSite) (h₂ : G₂.IsQuasicoherentOnSite)
    (hG : G.IsQuasicoherentOnSite) : P.IsQuasicoherentOnSite := by
  have hbip : (G₁ ⊞ G₂).IsQuasicoherentOnSite :=
    SheafOfModules.isQuasicoherentOnSite_biprod h₁ h₂
  have hcart : IsCartesianOnAffineCharts (pullback f g) := by
    refine isCartesianOnAffineCharts_of_isLimit
      (ι := Abelian.PullbackToBiproductIsKernel.pullbackToBiproduct f g)
      (φ := biprod.desc f (-g)) ?_ ?_
      (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF _ hbip)
      (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF _ hG)
    · exact (Abelian.PullbackToBiproductIsKernel.pullbackToBiproductFork f g).condition
    · exact Abelian.PullbackToBiproductIsKernel.isLimitPullbackToBiproduct _ _
  exact isQuasicoherentOnSite_of_isCartesianOnAffineCharts _
    (IsCartesianOnAffineCharts.of_iso h.isoPullback.symm hcart)

/-- **The meet of two quasi-coherent sheaves of submodules of a quasi-coherent `𝒪_F`-module is
quasi-coherent.**  The meet is the fibre product of the two inclusions, by
`Stacks.SheafOfModules.isPullback_submoduleInf`, and a fibre product of quasi-coherent modules
is quasi-coherent.

Quasi-coherence of the ambient module is used: it is the fourth corner of the cartesian square.
For submodules of the structure sheaf it is automatic; see
`AlgebraicGeometry.Space.isQuasicoherentOnSite_idealInf`. -/
theorem isQuasicoherentOnSite_inf {M : Modules.{u, u} B S hS F hF}
    (hM : M.IsQuasicoherentOnSite) (N₁ N₂ : M.Submodule)
    (h₁ : N₁.toSheafOfModules.IsQuasicoherentOnSite)
    (h₂ : N₂.toSheafOfModules.IsQuasicoherentOnSite) :
    (N₁ ⊓ N₂).toSheafOfModules.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_isPullback B S hS F hF
    (Stacks.SheafOfModules.isPullback_submoduleInf N₁ N₂) h₁ h₂ hM

variable (X : AlgebraicSpaces B S hS)

/-- **The meet of two quasi-coherent sheaves of ideals of `𝒪_X` is quasi-coherent.**

This is `AlgebraicGeometry.Space.isQuasicoherentOnSite_inf` with the structure sheaf as the
ambient module, whose quasi-coherence is `SheafOfModules.isQuasicoherentOnSite_unit`.  Nothing
is assumed beyond quasi-coherence of the two sheaves of ideals. -/
theorem isQuasicoherentOnSite_idealInf
    (I₁ I₂ : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (h₁ : I₁.toSheafOfModules.IsQuasicoherentOnSite)
    (h₂ : I₂.toSheafOfModules.IsQuasicoherentOnSite) :
    (I₁ ⊓ I₂).toSheafOfModules.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_inf B S hS X.1 X.2
    (SheafOfModules.isQuasicoherentOnSite_unit (structureRingSheaf B S hS X)) I₁ I₂ h₁ h₂

/-- **The meet of two quasi-coherent sheaves of ideals of `𝒪_X`**, as a quasi-coherent sheaf of
ideals: the meet of the two sheaves of submodules of `𝒪_X`, together with its quasi-coherence
from `AlgebraicGeometry.Space.isQuasicoherentOnSite_idealInf`. -/
def quasicoherentIdealsInf (I₁ I₂ : QuasicoherentIdeals B S hS X) :
    QuasicoherentIdeals B S hS X :=
  ⟨I₁.1 ⊓ I₂.1, isQuasicoherentOnSite_idealInf B S hS X I₁.1 I₂.1 I₁.2 I₂.2⟩

/-- The quasi-coherent sheaves of ideals of `𝒪_X` are closed under meets, so they carry the
`⊓` of `AlgebraicGeometry.Space.quasicoherentIdealsInf`. -/
instance quasicoherentIdealsMin : Min (QuasicoherentIdeals B S hS X) :=
  ⟨quasicoherentIdealsInf B S hS X⟩

/-- The sheaf of ideals underlying a meet of quasi-coherent sheaves of ideals is the meet of the
two underlying sheaves of ideals. -/
@[simp]
theorem coe_quasicoherentIdealsInf (I₁ I₂ : QuasicoherentIdeals B S hS X) :
    (I₁ ⊓ I₂).1 = I₁.1 ⊓ I₂.1 := rfl

/-- The meet of two quasi-coherent sheaves of ideals is contained in the first. -/
theorem quasicoherentIdealsInf_le_left (I₁ I₂ : QuasicoherentIdeals B S hS X) : I₁ ⊓ I₂ ≤ I₁ :=
  Subtype.coe_le_coe.1
    (le_of_eq_of_le (coe_quasicoherentIdealsInf B S hS X I₁ I₂) inf_le_left)

/-- The meet of two quasi-coherent sheaves of ideals is contained in the second. -/
theorem quasicoherentIdealsInf_le_right (I₁ I₂ : QuasicoherentIdeals B S hS X) : I₁ ⊓ I₂ ≤ I₂ :=
  Subtype.coe_le_coe.1
    (le_of_eq_of_le (coe_quasicoherentIdealsInf B S hS X I₁ I₂) inf_le_right)

end AlgebraicGeometry.Space

end
