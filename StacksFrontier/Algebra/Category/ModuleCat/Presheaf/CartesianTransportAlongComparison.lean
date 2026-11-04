module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianRestriction
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.RestrictScalarsBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.TerminalBaseChangeOfLocallyBijectivePullback

/-!
# The base-change comparison of a restriction map, read through two restrictions

Let `R` be a presheaf of commutative rings on a category `𝒳` and `M` a presheaf of modules over
it. Restrict `M` along two functors `q₁ : C ⥤ 𝒳` and `q₂ : D ⥤ 𝒳` and move the scalars along
isomorphisms `ψ₁ : O ≅ q₁^* R`, `ψ₂ : O' ≅ q₂^* R`, obtaining modules `G` on `C` and `H` on `D`.
Suppose a morphism `d : G ⟶ b_* H` over a ring map `ρ : O ⟶ b^* O'` along `b : C ⥤ D` is, over an
object `X` of `C`, the restriction map of `M` along an arrow `φ' : q₂(b X) ⟶ q₁(X)` of `𝒳`, and
`ρ` over `X` is the restriction of `R` along `φ'` read through `ψ₁` and `ψ₂`. Then the base change
`O'(b X) ⊗_{O(X)} G(X) ⟶ H(b X)` of `d` over `X` is bijective exactly when `M` is cartesian along
`φ'`: the two maps differ by the transport of tensor products along the ring isomorphisms.

## Main results

* `Stacks.RingSquare.bijective_iff_of_tmul`: two additive maps out of tensor products related by
  `Stacks.RingSquare.tensorMap` are simultaneously bijective.
* `Stacks.PresheafOfModules.bijective_extendScalars_iff_bijective_restrictionBaseChange`: the base
  change of `d` over `X` is bijective if and only if `M` is cartesian along `φ'`.
* `PresheafOfModules.bijective_restrictionBaseChange_of_isLocallyBijective_pullbackComparison`:
  for `X` and `b X` terminal and the mate `b^* G ⟶ H` of `d` locally bijective, `M` is cartesian
  along `φ'`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe t r u₁ v₁ u₂ v₂ u₃ v₃

namespace Stacks.RingSquare

variable {A A' B B' : Type*} {P Q : Type*}
  [CommRing A] [CommRing A'] [CommRing B] [CommRing B'] [AddCommGroup P] [AddCommGroup Q]
  [Module A A'] [Module B B'] [Module A P] [Module B P]

/-- Two additive maps out of tensor products related by the transport
`Stacks.RingSquare.tensorMap` along a square of ring maps with invertible vertical maps are
simultaneously bijective. -/
theorem bijective_iff_of_tmul (a : A →+* A') (b : B →+* B') (α : A ≃+* B) (β : A' ≃+* B')
    (hsq : ∀ t, β (a t) = b (α t))
    (hA : ∀ (t : A) (c : A'), t • c = a t * c)
    (hB : ∀ (s : B) (d : B'), s • d = b s * d)
    (hP : ∀ (t : A) (x : P), t • x = α t • x)
    (δ : TensorProduct A A' P →+ Q) (θ : TensorProduct B B' P →+ Q)
    (h : ∀ (c : A') (x : P), θ (β c ⊗ₜ[B] x) = δ (c ⊗ₜ[A] x)) :
    Function.Bijective δ ↔ Function.Bijective θ := by
  have hcomp (z) : θ (tensorMap a b α β hsq hA hB hP z) = δ z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul c x => exact h c x
    | add z z' hz hz' => rw [map_add, map_add, hz, hz', map_add]
  rw [← funext hcomp]
  exact Function.Bijective.of_comp_iff _ (bijective_tensorMap a b α β hsq hA hB hP)

end Stacks.RingSquare

namespace Stacks.PresheafOfModules

variable {𝒳 : Type u₁} [Category.{v₁} 𝒳] {C : Type u₂} [Category.{v₂} C]
  {D : Type u₃} [Category.{v₃} D]
  (R : 𝒳ᵒᵖ ⥤ CommRingCat.{r}) (M : PresheafOfModules.{max t r} (R ⋙ forget₂ CommRingCat RingCat))
  {O : Cᵒᵖ ⥤ RingCat.{r}} [Stacks.TerminalBaseChange.CommSections O]
  {O' : Dᵒᵖ ⥤ RingCat.{r}} [Stacks.TerminalBaseChange.CommSections O'] (q₁ : C ⥤ 𝒳) (q₂ : D ⥤ 𝒳)
  (ψ₁ : O ≅ q₁.op ⋙ R ⋙ forget₂ CommRingCat RingCat)
  (ψ₂ : O' ≅ q₂.op ⋙ R ⋙ forget₂ CommRingCat RingCat)
  (b : C ⥤ D) (ρ : O ⟶ b.op ⋙ O')

/-- **The base change of a comparison read through two restrictions is the base-change
comparison of the original module along the comparing arrow.** -/
theorem bijective_extendScalars_iff_bijective_restrictionBaseChange (X : C)
    (φ' : q₂.obj (b.obj X) ⟶ q₁.obj X)
    (hρ : ∀ t, (ψ₂.hom.app (op (b.obj X))).hom ((ρ.app (op X)).hom t) =
      (R.map φ'.op).hom ((ψ₁.hom.app (op X)).hom t))
    (d : (_root_.PresheafOfModules.restrictScalars ψ₁.hom).obj
        ((_root_.PresheafOfModules.pushforward₀ q₁ (R ⋙ forget₂ CommRingCat RingCat)).obj M) ⟶
      (_root_.PresheafOfModules.pushforward ρ).obj
        ((_root_.PresheafOfModules.restrictScalars ψ₂.hom).obj
          ((_root_.PresheafOfModules.pushforward₀ q₂ (R ⋙ forget₂ CommRingCat RingCat)).obj M)))
    (hd : ∀ g, (d.app (op X)).hom g = M.map φ'.op g) :
    Function.Bijective (((ModuleCat.extendRestrictScalarsAdj.{max t r, r, r}
      (ρ.app (op X)).hom).homEquiv _ _).symm (d.app (op X))).hom ↔
      Function.Bijective (restrictionBaseChange.{u₁, v₁, r, t} (R := R) M φ'.op) := by
  let _ : Module (O.obj (op X)) ((b.op ⋙ O').obj (op X)) :=
    Module.compHom _ (ρ.app (op X)).hom
  let _ : Module (R.obj (op (q₁.obj X))) (R.obj (op (q₂.obj (b.obj X)))) :=
    Module.compHom _ (R.map φ'.op).hom
  let _ : Module (O.obj (op X)) (M.obj (op (q₁.obj X))) :=
    Module.compHom _ (ψ₁.hom.app (op X)).hom
  let α : O.obj (op X) ≃+* R.obj (op (q₁.obj X)) := (ψ₁.app (op X)).ringCatIsoToRingEquiv
  let β : O'.obj (op (b.obj X)) ≃+* R.obj (op (q₂.obj (b.obj X))) :=
    (ψ₂.app (op (b.obj X))).ringCatIsoToRingEquiv
  exact Stacks.RingSquare.bijective_iff_of_tmul (P := M.obj (op (q₁.obj X)))
    (ρ.app (op X)).hom (R.map φ'.op).hom α β hρ (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl)
    (((ModuleCat.extendRestrictScalarsAdj.{max t r, r, r}
      (ρ.app (op X)).hom).homEquiv _ _).symm (d.app (op X))).hom.toAddMonoidHom
    (restrictionBaseChange.{u₁, v₁, r, t} (R := R) M φ'.op).hom.toAddMonoidHom
    fun c g => (restrictionBaseChange_tmul.{u₁, v₁, r, t} (R := R) M φ'.op (β c) g).trans
      (congrArg (fun z : M.obj (op (q₂.obj (b.obj X))) => β c • z) (hd g)).symm

/-- **Flat base change makes a module cartesian along the comparing arrow.** In the situation of
`Stacks.PresheafOfModules.bijective_extendScalars_iff_bijective_restrictionBaseChange`, with `X`
and `b X` terminal, suppose the mate `b^* G ⟶ H` of `d` is locally bijective, `G` and `H` are
locally their base changes from the terminal objects, `b_*` preserves sheaves and every
`O'(b X)`-module is the module of sections over `b X` of a sheaf. Then `M` is cartesian along
`φ'`. -/
theorem bijective_restrictionBaseChange_of_isLocallyBijective_pullbackComparison
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [J.WEqualsLocallyBijective AddCommGrpCat.{max t r}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{max t r}]
    {X : C} (hX : IsTerminal X) (hbX : IsTerminal (b.obj X))
    [(_root_.PresheafOfModules.pushforward.{max t r} ρ).IsRightAdjoint]
    (φ' : q₂.obj (b.obj X) ⟶ q₁.obj X)
    (hρ : ∀ t, (ψ₂.hom.app (op (b.obj X))).hom ((ρ.app (op X)).hom t) =
      (R.map φ'.op).hom ((ψ₁.hom.app (op X)).hom t))
    (d : (_root_.PresheafOfModules.restrictScalars ψ₁.hom).obj
        ((_root_.PresheafOfModules.pushforward₀ q₁ (R ⋙ forget₂ CommRingCat RingCat)).obj M) ⟶
      (_root_.PresheafOfModules.pushforward ρ).obj
        ((_root_.PresheafOfModules.restrictScalars ψ₂.hom).obj
          ((_root_.PresheafOfModules.pushforward₀ q₂ (R ⋙ forget₂ CommRingCat RingCat)).obj M)))
    (hd : ∀ g, (d.app (op X)).hom g = M.map φ'.op g)
    [hcs : _root_.PresheafOfModules.IsLocallySurjective K
      (((_root_.PresheafOfModules.pullbackPushforwardAdjunction.{max t r} ρ).homEquiv _ _).symm d)]
    [hci : _root_.PresheafOfModules.IsLocallyInjective K
      (((_root_.PresheafOfModules.pullbackPushforwardAdjunction.{max t r} ρ).homEquiv _ _).symm d)]
    [hGs : _root_.PresheafOfModules.IsLocallySurjective J
      ((Stacks.TerminalBaseChange.baseChangeAdj.{t} O hX).counit.app
        ((_root_.PresheafOfModules.restrictScalars ψ₁.hom).obj
          ((_root_.PresheafOfModules.pushforward₀ q₁ (R ⋙ forget₂ CommRingCat RingCat)).obj M)))]
    [hGi : _root_.PresheafOfModules.IsLocallyInjective J
      ((Stacks.TerminalBaseChange.baseChangeAdj.{t} O hX).counit.app
        ((_root_.PresheafOfModules.restrictScalars ψ₁.hom).obj
          ((_root_.PresheafOfModules.pushforward₀ q₁ (R ⋙ forget₂ CommRingCat RingCat)).obj M)))]
    [hHs : _root_.PresheafOfModules.IsLocallySurjective K
      ((Stacks.TerminalBaseChange.baseChangeAdj.{t} O' hbX).counit.app
        ((_root_.PresheafOfModules.restrictScalars ψ₂.hom).obj
          ((_root_.PresheafOfModules.pushforward₀ q₂ (R ⋙ forget₂ CommRingCat RingCat)).obj M)))]
    [hHi : _root_.PresheafOfModules.IsLocallyInjective K
      ((Stacks.TerminalBaseChange.baseChangeAdj.{t} O' hbX).counit.app
        ((_root_.PresheafOfModules.restrictScalars ψ₂.hom).obj
          ((_root_.PresheafOfModules.pushforward₀ q₂ (R ⋙ forget₂ CommRingCat RingCat)).obj M)))]
    (hpush : ∀ Q : _root_.PresheafOfModules.{max t r} O', Presheaf.IsSheaf K Q.presheaf →
      Presheaf.IsSheaf J ((_root_.PresheafOfModules.pushforward.{max t r} ρ).obj Q).presheaf)
    (htilde : ∀ Y : ModuleCat.{max t r} (O'.obj (op (b.obj X))),
      ∃ Q : _root_.PresheafOfModules.{max t r} O', Presheaf.IsSheaf K Q.presheaf ∧
        Nonempty (Q.obj (op (b.obj X)) ≅ Y)) :
    Function.Bijective (restrictionBaseChange.{u₁, v₁, r, t} (R := R) M φ'.op) := by
  have key := Stacks.TerminalBaseChange.isIso_extendScalars_of_isLocallyBijective_pullbackComparison
    hX hbX ρ _ _ d hpush htilde
  rw [ConcreteCategory.isIso_iff_bijective] at key
  exact (bijective_extendScalars_iff_bijective_restrictionBaseChange R M q₁ q₂ ψ₁ ψ₂ b ρ X φ'
    hρ d hd).mp key

end Stacks.PresheafOfModules
