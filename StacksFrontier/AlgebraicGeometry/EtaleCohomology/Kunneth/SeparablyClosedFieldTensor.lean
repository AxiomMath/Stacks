module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleCoefficientsPoint
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.SeparablyClosedFieldModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ModelComparison
public import StacksFrontier.Homology.KFlat.BifunctorTransportEquivalence
public import StacksFrontier.Homology.Tor.CanonicalTensorDerivedBifunctor

/-!
# `D((Spec k)_étale, Λ) ≃ D(Λ)` is compatible with `⊗^L`

Let `k` be a separably closed field and `Λ` a commutative ring. The equivalence
`Stacks.EtaleCohomology.EtaleCoefficients.derivedModulesEquivOfSepClosed :
D((Spec k)_étale, Λ) ≌ D(Λ)`, through which [Stacks, Tag 0F1P] reads `RΓ(X, E)` as an object of
`D(Λ)`, is induced by the equivalence `F : Mod((Spec k)_étale, Λ̲) ≌ Mod(Λ)` of sections at the
terminal object. This file proves that it carries the derived tensor product `⊗^L_Λ` of
`D((Spec k)_étale, Λ)` (`Stacks.EtaleCohomology.EtaleCoefficients.tensor`) to the canonical derived
tensor product of `D(Λ)` (`CochainComplex.DerivedTensor.canonicalDerivedTensorProduct`).

## Main definitions

All in the namespace `Stacks.EtaleCohomology.EtaleCoefficients`.

* `sepClosedPointTensorIso` — `F(A ⊗ B) ≅ F A ⊗_Λ F B` on sheaves of modules.
* `derivedModulesEquivOfSepClosedTensorIso` — **`Φ(K ⊗^L L) ≅ Φ K ⊗^L Φ L`** for
  `Φ = derivedModulesEquivOfSepClosed`, as an isomorphism of bifunctors on
  `D((Spec k)_étale, Λ)`.

## Main results

* `id_mem_of_mem_topology_terminal` — the terminal object of `(Spec k)_étale` is covered only by
  itself.
* `bijective_app_of_forall_id_mem` — a locally bijective map of presheaves is bijective at such an
  object; applied to the sheafification units of the constant presheaf of rings and of the
  presheaf tensor product.

## Implementation notes

The sheaf tensor product is the sheafification of the objectwise tensor product, and at an object
covered only by itself sheafification changes nothing; so `F(A ⊗ B)` is `A(pt) ⊗_{Λ̲(pt)} B(pt)`,
and `Λ̲(pt) = Λ`. This is `sepClosedPointTensorIso`, natural in both variables. The derived
statement is the transport of the derived bifunctor along an equivalence of abelian categories
carrying one tensor product to the other,
`CochainComplex.KFlatBifunctor.derivedTransportIsoOfEquivalence`, composed with the identification
of the derived tensor product of a ringed site with the K-flat derived bifunctor
(`Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorIsoDerivedBifunctor`) and of the
latter with the canonical derived tensor product of `D(Λ)`
(`CochainComplex.DerivedTensor.derivedBifunctorCanonicalTensorIso`).

*The two point equivalences.* `Stacks.EtaleCohomology.EtaleCoefficients.pointDerivedEquivalence`
is `D(Λ(pt)) ≌ D(pt, Λ)`, for the one-point ringed topos `(pt, Λ)` with ring of sections
`Λ(pt) = pointScalars Λ`; `derivedModulesEquivOfSepClosed` is `D((Spec k)_étale, Λ) ≌ D(Λ)`. Their
sources and targets are different categories (the point topos and the étale topos of `Spec k`),
so neither restates the other, and no third equivalence is introduced here.

## References

* [Stacks Project, Tag 0F1P](https://stacks.math.columbia.edu/tag/0F1P)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct

universe u

namespace Stacks.EtaleCohomology.EtaleCoefficients

section Bijective

variable {C : Type*} [Category C] {J : GrothendieckTopology C}
  {D : Type*} [Category D] {FD : D → D → Type*} {CD : D → Type*}
  [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory D FD]

/-- **A locally bijective map of presheaves is bijective at an object covered only by itself**:
if every covering sieve of `U` contains `𝟙 U`, local injectivity and local surjectivity at `U`
are injectivity and surjectivity. -/
theorem bijective_app_of_forall_id_mem {F G : Cᵒᵖ ⥤ D} (φ : F ⟶ G)
    [Presheaf.IsLocallyInjective J φ] [Presheaf.IsLocallySurjective J φ] {U : C}
    (hU : ∀ S ∈ J U, S (𝟙 U)) : Function.Bijective (φ.app (op U)) := by
  refine ⟨fun x y hxy => ?_, fun s => ?_⟩
  · simpa using hU _ (Presheaf.equalizerSieve_mem J φ x y hxy)
  · obtain ⟨t, ht⟩ := hU _ (Presheaf.imageSieve_mem J φ s)
    exact ⟨t, by simpa using ht⟩

end Bijective

variable (k : Type u) [Field k] [IsSepClosed k]

/-- **The terminal object of `(Spec k)_étale` is covered only by itself**, `k` being separably
closed: every covering sieve of it contains the identity. A covering sieve, read on the cover-dense
subsite of the terminal object, is a covering sieve of the one-object category with the induced
topology, which is trivial (`inducedTopology_pointFunctor_eq_bot`); so it contains a map with a
section, hence the identity. -/
theorem id_mem_of_mem_topology_terminal (S : Sieve ((fromEtale (Spec (.of k))).obj
      (SepClosedField.terminal k)))
    (hS : S ∈ topology (Spec (.of k)) ((fromEtale (Spec (.of k))).obj
      (SepClosedField.terminal k))) :
    S (𝟙 _) := by
  let E := SepClosedField.terminal k
  let i : E ≅ (toEtale (Spec (.of k))).obj ((fromEtale (Spec (.of k))).obj E) :=
    (equiv (Spec (.of k))).unitIso.app E
  have h₁ : S.functorPushforward (toEtale (Spec (.of k))) ∈
      smallEtaleTopology (Spec (.of k)) ((toEtale (Spec (.of k))).obj
        ((fromEtale (Spec (.of k))).obj E)) :=
    (Functor.mem_inducedTopology_iff_of_isCoverDense _ _ _).1 hS
  have h₂ := (smallEtaleTopology (Spec (.of k))).pullback_stable i.hom h₁
  have h₃ := Functor.IsCoverDense.functorPullback_pushforward_covering
    (G := SepClosedField.pointFunctor k) (K := smallEtaleTopology (Spec (.of k))) (X := ⟨⟨⟩⟩)
    ⟨_, h₂⟩
  have h₄ : ((S.functorPushforward (toEtale (Spec (.of k)))).pullback i.hom).functorPullback
      (SepClosedField.pointFunctor k) ∈
        (SepClosedField.pointFunctor k).inducedTopology (smallEtaleTopology (Spec (.of k)))
          ⟨⟨⟩⟩ := (Functor.mem_inducedTopology_iff_of_isCoverDense _ _ _).2 h₃
  rw [inducedTopology_pointFunctor_eq_bot, GrothendieckTopology.bot_covering] at h₄
  have h₅ : ((S.functorPushforward (toEtale (Spec (.of k)))).pullback i.hom).functorPullback
      (SepClosedField.pointFunctor k) (𝟙 ⟨⟨⟩⟩) := by
    rw [h₄]
    trivial
  obtain ⟨Z, g, h, hg, hgh⟩ := h₅
  have hsec : (toEtale (Spec (.of k))).map
      ((toEtale (Spec (.of k))).preimage (i.inv ≫ h) ≫ g) = 𝟙 _ := by
    rw [Functor.map_comp, Functor.map_preimage, Category.assoc, ← hgh]
    simp
  have hid : (toEtale (Spec (.of k))).preimage (i.inv ≫ h) ≫ g = 𝟙 _ :=
    (toEtale (Spec (.of k))).map_injective (hsec.trans (CategoryTheory.Functor.map_id _ _).symm)
  rw [← hid]
  exact S.downward_closed hg _

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The terminal object `Spec k` of the small model of `(Spec k)_étale`. -/
abbrev sepClosedPoint : Site (Spec (.of k)) :=
  (fromEtale (Spec (.of k))).obj (SepClosedField.terminal k)


/-- The comparison `Λ ⟶ Λ̲(Spec k)` of the constant presheaf of rings with the constant sheaf is
bijective at the terminal object. -/
theorem bijective_constantRingSheafMap_app :
    Function.Bijective ((Stacks.ConstantSheaf.constantRingSheafMap (topology (Spec (.of k))) Λ).app
        (op (sepClosedPoint k))) :=
  bijective_app_of_forall_id_mem (J := topology (Spec (.of k))) _
    (id_mem_of_mem_topology_terminal k)


section Tensor

variable (A B : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (ringedTopos Λ (Spec (.of k))).O))

/-- The ring of the point, `Λ̲(pt)`, spelled as the presheaf tensor product spells it. -/
abbrev sepClosedPointRing : RingCat.{u + 1} :=
  ((ringedTopos Λ (Spec (.of k))).O.obj ⋙ forget₂ CommRingCat RingCat).obj (op (sepClosedPoint k))

/-- The sections at the point of a sheaf of modules, as a module over `sepClosedPointRing`. -/
def sepClosedPointSections (M : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (ringedTopos Λ (Spec (.of k))).O)) : ModuleCat.{u + 1} (sepClosedPointRing k Λ) :=
  M.val.obj (op (sepClosedPoint k))

/-- The sheafification unit of the presheaf tensor product, at the point. -/
def sepClosedTensorUnit :
    ModuleCat.of (sepClosedPointRing k Λ)
        (sepClosedPointSections k Λ A ⊗[sepClosedPointRing k Λ] sepClosedPointSections k Λ B) ⟶
      sepClosedPointSections k Λ
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u + 1, u + 1, u + 1, u + 1}
          (ringedTopos Λ (Spec (.of k))).O).obj A).obj B) :=
  ((PresheafOfModules.sheafificationAdjunction.{u + 1}
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Λ (Spec (.of k))).O).obj)).unit.app
    (PresheafOfModules.tensorObj (O := (ringedTopos Λ (Spec (.of k))).O.obj) A.val B.val)).app
      (op (sepClosedPoint k))

/-- The sheafification unit of the presheaf tensor product is bijective at the terminal object. -/
theorem bijective_sepClosedTensorUnit : Function.Bijective (sepClosedTensorUnit k Λ A B).hom :=
  bijective_app_of_forall_id_mem (J := topology (Spec (.of k)))
    (CategoryTheory.toSheafify (topology (Spec (.of k)))
      (PresheafOfModules.tensorObj (O := (ringedTopos Λ (Spec (.of k))).O.obj)
        A.val B.val).presheaf)
    (id_mem_of_mem_topology_terminal k)

/-- The ring map `Λ ⟶ Λ̲(pt)`. -/
abbrev sepClosedPointRingMap : Λ →+* sepClosedPointRing k Λ :=
  ((Stacks.ConstantSheaf.constantRingSheafMap (topology (Spec (.of k))) Λ).app
    (op (sepClosedPoint k))).hom

/-- The pairing `F A × F B ⟶ F (A ⊗ B)` through the presheaf tensor product at the point. -/
def sepClosedPointTensorPairing :
    (modulesEquivOfSepClosed k Λ).functor.obj A →ₗ[Λ]
      (modulesEquivOfSepClosed k Λ).functor.obj B →ₗ[Λ]
        (modulesEquivOfSepClosed k Λ).functor.obj
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u + 1, u + 1, u + 1, u + 1}
            (ringedTopos Λ (Spec (.of k))).O).obj A).obj B) :=
  LinearMap.mk₂ Λ
    (fun x y => (sepClosedTensorUnit k Λ A B).hom
      ((show sepClosedPointSections k Λ A from x) ⊗ₜ[sepClosedPointRing k Λ]
        (show sepClosedPointSections k Λ B from y)))
    (fun x x' y => (congrArg (sepClosedTensorUnit k Λ A B).hom
      (TensorProduct.add_tmul (show sepClosedPointSections k Λ A from x)
        (show sepClosedPointSections k Λ A from x')
        (show sepClosedPointSections k Λ B from y))).trans
      (map_add _ _ _))
    (fun r x y => (congrArg (sepClosedTensorUnit k Λ A B).hom
      (TensorProduct.smul_tmul' (sepClosedPointRingMap k Λ r)
        (show sepClosedPointSections k Λ A from x)
        (show sepClosedPointSections k Λ B from y)).symm).trans
      ((sepClosedTensorUnit k Λ A B).hom.map_smul (sepClosedPointRingMap k Λ r) _))
    (fun x y y' => (congrArg (sepClosedTensorUnit k Λ A B).hom
      (TensorProduct.tmul_add (show sepClosedPointSections k Λ A from x)
        (show sepClosedPointSections k Λ B from y)
        (show sepClosedPointSections k Λ B from y'))).trans
      (map_add _ _ _))
    (fun r x y => (congrArg (sepClosedTensorUnit k Λ A B).hom
      (TensorProduct.tmul_smul (R := sepClosedPointRing k Λ) (R' := sepClosedPointRing k Λ)
        (sepClosedPointRingMap k Λ r) (show sepClosedPointSections k Λ A from x)
        (show sepClosedPointSections k Λ B from y))).trans
      ((sepClosedTensorUnit k Λ A B).hom.map_smul (sepClosedPointRingMap k Λ r) _))

/-- The ring map `Λ ⟶ Λ̲(Spec k)` is surjective. -/
theorem surjective_sepClosedPointRingMap : Function.Surjective (sepClosedPointRingMap k Λ) :=
  (bijective_constantRingSheafMap_app k Λ).2

/-- The inverse direction, from the presheaf tensor product at the point. -/
def sepClosedPointTensorInv :
    sepClosedPointSections k Λ A ⊗[sepClosedPointRing k Λ] sepClosedPointSections k Λ B →+
      ((modulesEquivOfSepClosed k Λ).functor.obj A ⊗[Λ]
        (modulesEquivOfSepClosed k Λ).functor.obj B) :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun m => AddMonoidHom.mk'
        (fun n => (show (modulesEquivOfSepClosed k Λ).functor.obj A from m) ⊗ₜ[Λ]
          (show (modulesEquivOfSepClosed k Λ).functor.obj B from n))
        (fun n n' => TensorProduct.tmul_add _ _ _))
      (fun m m' => AddMonoidHom.ext fun n => TensorProduct.add_tmul _ _ _))
    (fun r m n => by
      obtain ⟨l, rfl⟩ := surjective_sepClosedPointRingMap k Λ r
      exact TensorProduct.smul_tmul (R := Λ) (R' := Λ) l
        (show (modulesEquivOfSepClosed k Λ).functor.obj A from m)
        (show (modulesEquivOfSepClosed k Λ).functor.obj B from n))

/-- The pairing, after the inverse direction, is the sheafification unit. -/
theorem lift_sepClosedPointTensorPairing_sepClosedPointTensorInv
    (w : sepClosedPointSections k Λ A ⊗[sepClosedPointRing k Λ] sepClosedPointSections k Λ B) :
    TensorProduct.lift (sepClosedPointTensorPairing k Λ A B) (sepClosedPointTensorInv k Λ A B w) =
      (sepClosedTensorUnit k Λ A B).hom w := by
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]; rfl
  | tmul x y => exact TensorProduct.lift.tmul _ _
  | add x y hx hy => rw [map_add, map_add, hx, hy]; exact (map_add _ _ _).symm

/-- The sheafification unit of the presheaf tensor product at the point, as a linear
equivalence. -/
def sepClosedTensorUnitEquiv :
    (sepClosedPointSections k Λ A ⊗[sepClosedPointRing k Λ] sepClosedPointSections k Λ B)
      ≃ₗ[sepClosedPointRing k Λ] sepClosedPointSections k Λ
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u + 1, u + 1, u + 1, u + 1}
          (ringedTopos Λ (Spec (.of k))).O).obj A).obj B) :=
  LinearEquiv.ofBijective (sepClosedTensorUnit k Λ A B).hom (bijective_sepClosedTensorUnit k Λ A B)

/-- **The equivalence of sections at the point is monoidal, on modules**:
`F A ⊗_Λ F B ≅ F (A ⊗ B)`, through the presheaf tensor product at the point, whose sheafification
unit is bijective there. -/
def sepClosedPointTensorLinearEquiv :
    ((modulesEquivOfSepClosed k Λ).functor.obj A ⊗[Λ]
        (modulesEquivOfSepClosed k Λ).functor.obj B) ≃ₗ[Λ]
      (modulesEquivOfSepClosed k Λ).functor.obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u + 1, u + 1, u + 1, u + 1}
          (ringedTopos Λ (Spec (.of k))).O).obj A).obj B) where
  __ := TensorProduct.lift (sepClosedPointTensorPairing k Λ A B)
  invFun z := sepClosedPointTensorInv k Λ A B ((sepClosedTensorUnitEquiv k Λ A B).symm z)
  left_inv z := by
    induction z using TensorProduct.induction_on with
    | zero =>
      change sepClosedPointTensorInv k Λ A B ((sepClosedTensorUnitEquiv k Λ A B).symm
        (TensorProduct.lift (sepClosedPointTensorPairing k Λ A B) 0)) = 0
      exact (congrArg
          (fun t => sepClosedPointTensorInv k Λ A B ((sepClosedTensorUnitEquiv k Λ A B).symm t))
        (map_zero (TensorProduct.lift (sepClosedPointTensorPairing k Λ A B)))).trans
        ((congrArg (sepClosedPointTensorInv k Λ A B)
          ((sepClosedTensorUnitEquiv k Λ A B).symm.map_zero)).trans
          (map_zero _))
    | tmul x y =>
      change sepClosedPointTensorInv k Λ A B ((sepClosedTensorUnitEquiv k Λ A B).symm
        ((sepClosedTensorUnitEquiv k Λ A B) (_ ⊗ₜ _))) = _
      rw [LinearEquiv.symm_apply_apply]
      rfl
    | add x y hx hy =>
      change sepClosedPointTensorInv k Λ A B ((sepClosedTensorUnitEquiv k Λ A B).symm
        (TensorProduct.lift (sepClosedPointTensorPairing k Λ A B) (x + y))) = x + y
      change sepClosedPointTensorInv k Λ A B ((sepClosedTensorUnitEquiv k Λ A B).symm
        (TensorProduct.lift (sepClosedPointTensorPairing k Λ A B) x)) = x at hx
      change sepClosedPointTensorInv k Λ A B ((sepClosedTensorUnitEquiv k Λ A B).symm
        (TensorProduct.lift (sepClosedPointTensorPairing k Λ A B) y)) = y at hy
      exact (congrArg
          (fun t => sepClosedPointTensorInv k Λ A B ((sepClosedTensorUnitEquiv k Λ A B).symm t))
        (map_add (TensorProduct.lift (sepClosedPointTensorPairing k Λ A B)) x y)).trans
        ((congrArg (sepClosedPointTensorInv k Λ A B)
          ((sepClosedTensorUnitEquiv k Λ A B).symm.map_add _ _)).trans
          (((sepClosedPointTensorInv k Λ A B).map_add _ _).trans (congrArg₂ (· + ·) hx hy)))
  right_inv z := by
    change TensorProduct.lift (sepClosedPointTensorPairing k Λ A B)
      (sepClosedPointTensorInv k Λ A B _) = z
    rw [lift_sepClosedPointTensorPairing_sepClosedPointTensorInv]
    exact (sepClosedTensorUnitEquiv k Λ A B).apply_symm_apply z

omit [IsSepClosed k] in
/-- The sheafification unit of the presheaf tensor product at the point is natural in both
factors. -/
theorem sepClosedTensorUnit_naturality {A' B' : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Λ (Spec (.of k))).O)}
    (f : A ⟶ A') (g : B ⟶ B') (x : sepClosedPointSections k Λ A)
    (y : sepClosedPointSections k Λ B) :
    (((PresheafOfModules.sheafification.{u + 1} (R := Stacks.SheafOfModules.Tensor.ringSheaf
          (ringedTopos Λ (Spec (.of k))).O)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Λ (Spec (.of k))).O).obj)).map
          (PresheafOfModules.tensorHom (O := (ringedTopos Λ (Spec (.of k))).O.obj)
            f.val g.val)).val.app
            (op (sepClosedPoint k))).hom ((sepClosedTensorUnit k Λ A B).hom (x ⊗ₜ y)) =
      (sepClosedTensorUnit k Λ A' B').hom
        ((show sepClosedPointSections k Λ A' from (f.val.app (op (sepClosedPoint k))).hom x) ⊗ₜ
          (show sepClosedPointSections k Λ B' from (g.val.app (op (sepClosedPoint k))).hom y)) := by
  have h := NatTrans.naturality (PresheafOfModules.sheafificationAdjunction.{u + 1}
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Λ (Spec (.of k))).O).obj)).unit
    (PresheafOfModules.tensorHom (O := (ringedTopos Λ (Spec (.of k))).O.obj) f.val g.val)
  have h' := congrArg (fun m => (m.app (op (sepClosedPoint k))).hom (x ⊗ₜ y)) h
  exact h'.symm.trans (congrArg (sepClosedTensorUnit k Λ A' B').hom
    (PresheafOfModules.tensorHom_tmul f.val g.val (op (sepClosedPoint k)) x y))

end Tensor

section Iso

/-- **`F(A ⊗ B) ≅ F A ⊗_Λ F B`** for the equivalence `F` of `modulesEquivOfSepClosed`. -/
def sepClosedPointTensorIso (A B : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (ringedTopos Λ (Spec (.of k))).O)) :
    (modulesEquivOfSepClosed k Λ).functor.obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u + 1, u + 1, u + 1, u + 1}
          (ringedTopos Λ (Spec (.of k))).O).obj A).obj B) ≅
      ((MonoidalCategory.curriedTensor (ModuleCat.{u + 1} Λ)).obj
        ((modulesEquivOfSepClosed k Λ).functor.obj A)).obj
          ((modulesEquivOfSepClosed k Λ).functor.obj B) :=
  (sepClosedPointTensorLinearEquiv k Λ A B).toModuleIso.symm

/-- A square of morphisms commutes if the square of inverses of the vertical isomorphisms does. -/
private theorem comp_hom_eq_hom_comp_of_inv_comp_eq {C : Type*} [Category C] {X Y X' Y' : C}
    (e : X ≅ Y) {e' : X' ≅ Y'} {f : X ⟶ X'} {g : Y ⟶ Y'} (h : e.inv ≫ f = g ≫ e'.inv) :
    f ≫ e'.hom = e.hom ≫ g := by
  rw [← cancel_epi e.inv, ← Category.assoc, h]
  simp

/-- `F(A ⊗ B) ≅ F A ⊗_Λ F B` is natural in `A`. -/
theorem sepClosedPointTensorIso_naturality_left {A A' : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Λ (Spec (.of k))).O)}
    (f : A ⟶ A') (B : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Λ (Spec (.of k))).O)) :
    (modulesEquivOfSepClosed k Λ).functor.map
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u + 1, u + 1, u + 1, u + 1}
          (ringedTopos Λ (Spec (.of k))).O).map f).app B) ≫ (sepClosedPointTensorIso k Λ A' B).hom =
      (sepClosedPointTensorIso k Λ A B).hom ≫
        ((MonoidalCategory.curriedTensor (ModuleCat.{u + 1} Λ)).map
          ((modulesEquivOfSepClosed k Λ).functor.map f)).app
            ((modulesEquivOfSepClosed k Λ).functor.obj B) := by
  refine comp_hom_eq_hom_comp_of_inv_comp_eq _
    (ModuleCat.hom_ext (TensorProduct.ext' fun x y => ?_))
  exact sepClosedTensorUnit_naturality k Λ A B f (𝟙 B) x y

/-- `F(A ⊗ B) ≅ F A ⊗_Λ F B` is natural in `B`. -/
theorem sepClosedPointTensorIso_naturality_right (A : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Λ (Spec (.of k))).O))
    {B B' : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Λ (Spec (.of k))).O)} (g : B ⟶ B') :
    (modulesEquivOfSepClosed k Λ).functor.map
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u + 1, u + 1, u + 1, u + 1}
          (ringedTopos Λ (Spec (.of k))).O).obj A).map g) ≫ (sepClosedPointTensorIso k Λ A B').hom =
      (sepClosedPointTensorIso k Λ A B).hom ≫
        ((MonoidalCategory.curriedTensor (ModuleCat.{u + 1} Λ)).obj
          ((modulesEquivOfSepClosed k Λ).functor.obj A)).map
            ((modulesEquivOfSepClosed k Λ).functor.map g) := by
  refine comp_hom_eq_hom_comp_of_inv_comp_eq _
    (ModuleCat.hom_ext (TensorProduct.ext' fun x y => ?_))
  exact sepClosedTensorUnit_naturality k Λ A B (𝟙 A) g x y

end Iso



section Derived

attribute [local instance] HasDerivedCategory.standard

/-- The equivalence of sections at the point is additive. -/
instance : (modulesEquivOfSepClosed k Λ).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Its inverse is additive. -/
instance : (modulesEquivOfSepClosed k Λ).inverse.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- **`D((Spec k)_étale, Λ) ≃ D(Λ)` is compatible with `⊗^L`.** -/
def derivedModulesEquivOfSepClosedTensorIso [HasDerivedCategory (ModuleCat.{u + 1} Λ)] :
    tensor Λ (Spec (.of k)) ⋙ (Functor.whiskeringRight _ _ _).obj
        (derivedModulesEquivOfSepClosed k Λ).functor ≅
      (derivedModulesEquivOfSepClosed k Λ).functor ⋙
        (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct Λ).tensor ⋙
          (Functor.whiskeringLeft _ _ _).obj (derivedModulesEquivOfSepClosed k Λ).functor :=
  letI := HasDerivedCategory.standard (SheafOfModules.{u + 1}
    (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Λ (Spec (.of k))).O))
  Functor.isoWhiskerRight
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorIsoDerivedBifunctor
        (ringedTopos Λ (Spec (.of k))).O (h := HasDerivedCategory.standard _)) _ ≪≫
    CochainComplex.KFlatBifunctor.derivedTransportIsoOfEquivalence
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u + 1, u + 1, u + 1, u + 1}
        (ringedTopos Λ (Spec (.of k))).O)
      (MonoidalCategory.curriedTensor (ModuleCat.{u + 1} Λ)) (modulesEquivOfSepClosed k Λ)
      (sepClosedPointTensorIso k Λ) (fun f b => sepClosedPointTensorIso_naturality_left k Λ f b)
      (fun a _ _ g => sepClosedPointTensorIso_naturality_right k Λ a g) ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
      (CochainComplex.DerivedTensor.derivedBifunctorCanonicalTensorIso Λ) _)

end Derived

end Stacks.EtaleCohomology.EtaleCoefficients
