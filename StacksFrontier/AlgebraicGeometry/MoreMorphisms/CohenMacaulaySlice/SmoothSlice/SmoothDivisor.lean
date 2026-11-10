module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Localization.Algebra
public import StacksFrontier.AlgebraicGeometry.AffineDifferentialsIso.Surjective
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier
public import StacksFrontier.AlgebraicGeometry.FiberCotangentAssembly.Basic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.EffectiveCartierSlice
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.RestrictOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.AtPoint
public import StacksFrontier.RingTheory.Derivation.Regularity
public import StacksFrontier.RingTheory.Flat.RegularSequenceOverBase
public import StacksFrontier.RingTheory.Smooth.RegularLocalRing
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.SmoothSlice.NonzeroDifferential
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Slicing a smooth morphism by a hypersurface: the slice

Transport of the nonzero-differential hypothesis to an affine neighbourhood, regularity of the
fibre local ring, the effective Cartier divisor cut out by the germ, smoothness of its
restriction to an affine open, and Stacks tag 057C,
`Stacks.AlgebraicGeometry.exists_smooth_effectiveCartierDivisor_of_nonzero_differential`.
The hypothesis `Stacks.AlgebraicGeometry.HasNonzeroRelativeDifferential` and the commutative
algebra used here are in
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.SmoothSlice.NonzeroDifferential`.

## References

* [Stacks Project, Tag 057C](https://stacks.math.columbia.edu/tag/057C)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped TensorProduct

namespace Stacks.AlgebraicGeometry

universe u

/-- **Two composites of restriction maps of `𝒪_X` between the same opens agree.**  A morphism
in `X.Opensᵒᵖ` carries no data beyond the inclusion it witnesses, so the two composites are the
same map however the intermediate open and the inclusions are written. -/
private theorem presheaf_map_comp_eq {X : Scheme.{u}} {A B C B' : X.Opensᵒᵖ}
    (i : A ⟶ B) (j : B ⟶ C) (i' : A ⟶ B') (j' : B' ⟶ C) :
    X.presheaf.map i ≫ X.presheaf.map j = X.presheaf.map i' ≫ X.presheaf.map j' :=
  (X.presheaf.map_comp i j).symm.trans (X.presheaf.map_comp i' j')

/-- **`f.appTop` followed by a restriction is `f.appLE` on that open.**

`AlgebraicGeometry.Scheme.Hom.appLE_eq_app` turns `f.app ⊤` into `f.appLE ⊤ (f ⁻¹ᵁ ⊤) _`, whose
codomain is `Γ(Y, f ⁻¹ᵁ ⊤)` rather than `Γ(Y, ⊤)`.  The two are the same ring, but not reducibly
so, which leaves the goal type-incorrect at the transparency `rw` checks it at;  rewriting by
`AlgebraicGeometry.Scheme.Hom.appLE_map` afterwards therefore fails.  Composing the two in term
mode instead keeps the whole chain at default transparency. -/
private theorem appTop_comp_map {Y X : Scheme.{u}} (f : Y ⟶ X) (V : Y.Opens) :
    f.appTop ≫ Y.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op =
      Scheme.Hom.appLE f ⊤ V le_top :=
  (congrArg (fun t => t ≫ Y.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op)
      (Scheme.Hom.appLE_eq_app f (U := ⊤)).symm).trans
    (Scheme.Hom.appLE_map f le_rfl _)

/-- **The scalar action on a stalk, at the scheme-level spelling of a sheaf of modules.**
The germ of `r • m` is the germ of `r` acting on the germ of `m`.

This is `PresheafOfModules.germ_smul` for `M.val`, restated over
`AlgebraicGeometry.Scheme.Modules.presheaf M` and the `Γ(X, U)`-action on `Γ(M, U)`.  Both
identifications hold by definition and neither holds reducibly: `Scheme.Modules.presheaf M` is
`M.val.presheaf`, and `Γ(X, U)` acts on `Γ(M, U)` through `ModuleCat.restrictScalars` along
`X.ringCatSheaf`.  So the `PresheafOfModules` form does not rewrite in a goal written with the
scheme-level spelling, and this one does. -/
private theorem Modules.germ_smul {X : Scheme.{u}} (M : X.Modules) (x : X)
    (U : X.Opens) (hx : x ∈ U) (r : Γ(X, U)) (m : Γ(M, U)) :
    letI : Module (X.presheaf.stalk x) (M.presheaf.stalk x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) M.val x
    (M.presheaf.germ U x hx).hom (r • m) =
      (X.presheaf.germ U x hx).hom r • (M.presheaf.germ U x hx).hom m :=
  PresheafOfModules.germ_smul M.val x U hx r m

/-- **The scalar action on the sections of a restriction along an open immersion of opens.**
`Γ(M.restrict U.ι, W)` and `Γ(M, U.ι ''ᵁ W)` are the same group of sections, and `Γ(U, W)` and
`Γ(X, U.ι ''ᵁ W)` the same ring of scalars, so `r • z` means the same thing on either side.

The two sides nevertheless carry different `Module` instances, the one
`AlgebraicGeometry.Scheme.Modules.restrictAppIso` relates them by, so neither side's scalar
action rewrites into the other's.  The right-hand instance is written out with `@HSMul.hSMul`
rather than reached by a type ascription, because an ascription to a definitionally equal type
leaves the instance that was already inferred in place. -/
private theorem Modules.smul_restrict_ι {X : Scheme.{u}} (U : X.Opens) (M : X.Modules)
    (W : U.toScheme.Opens) (r : Γ(U.toScheme, W)) (z : Γ(M.restrict U.ι, W)) :
    ((r • z : Γ(M.restrict U.ι, W)) : Γ(M, U.ι ''ᵁ W)) =
      @HSMul.hSMul Γ(X, U.ι ''ᵁ W) Γ(M, U.ι ''ᵁ W) Γ(M, U.ι ''ᵁ W) _ r z := by
  have hs := M.smul_restrictAppIso_hom_apply U.ι W r z
  simp only [Scheme.Opens.ι_appIso, Iso.refl_inv, Scheme.Modules.restrictAppIso,
    Iso.refl_hom] at hs
  exact hs

/-- **The germ of a section through the stalk comparison along an open immersion.**
Let `f : X ⟶ Y` be an open immersion, `M` a sheaf of `𝒪_Y`-modules, `N` a sheaf of
`𝒪_X`-modules and `φ : N ⟶ M.restrict f`.  The map `N_x ⟶ M_{f x}` obtained from `φ` on stalks
followed by the comparison `(M.restrict f)_x ≅ M_{f x}` carries the germ at `x` of a section `b`
of `N` on `W` to the germ at `f x` of `φ b` on `f ''ᵁ W`.

This chains `TopCat.Presheaf.stalkFunctor_map_germ` with
`AlgebraicGeometry.Scheme.Modules.germ_restrictStalkNatIso_hom_app`.  Both halves are stated
over `(Scheme.Modules.toPresheaf X).obj _` rather than
`AlgebraicGeometry.Scheme.Modules.presheaf _`, which is the same abelian presheaf but not
reducibly so, so neither rewrites in a goal written with the latter;  the composite is proved
here once, by application rather than by rewriting, and is used as a closed equation. -/
private theorem Modules.germ_stalkMap_restrictStalkNatIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (M : Y.Modules) (N : X.Modules) (φ : N ⟶ M.restrict f)
    (x : X) (W : X.Opens) (hxW : x ∈ W) (b : Γ(N, W)) :
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          ((Scheme.Modules.toPresheaf _).map φ) ≫
        (Scheme.Modules.restrictStalkNatIso f x).hom.app M).hom
      ((N.presheaf.germ W x hxW).hom b) =
      (M.presheaf.germ (f ''ᵁ W) (f x) ⟨x, hxW, rfl⟩).hom (φ.app W b) :=
  (congrArg ((Scheme.Modules.restrictStalkNatIso f x).hom.app M).hom
      (TopCat.Presheaf.stalkFunctor_map_germ_apply (C := AddCommGrpCat) W x hxW
        ((Scheme.Modules.toPresheaf _).map φ) b)).trans
    (ConcreteCategory.congr_hom
      (Scheme.Modules.germ_restrictStalkNatIso_hom_app f x M hxW) (φ.app W b))

private theorem restrict_stalkMap_smul {X : Scheme.{u}} (U : X.Opens)
    (M : X.Modules) (N : U.toScheme.Modules) (φ : N ⟶ M.restrict U.ι)
    (x : U.toScheme) (r : U.toScheme.presheaf.stalk x)
    (m : N.presheaf.stalk x) :
    letI : Module (U.toScheme.presheaf.stalk x) (N.presheaf.stalk x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := U.toScheme.presheaf) N.val x
    letI : Module (X.presheaf.stalk x.1) (M.presheaf.stalk x.1) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) M.val x.1
    let F : N.presheaf.stalk x ⟶ M.presheaf.stalk x.1 :=
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      ((Scheme.Modules.toPresheaf _).map φ) ≫
        (Scheme.Modules.restrictStalkNatIso U.ι x).hom.app M
    F.hom (r • m) = (U.stalkIso x).hom.hom r • F.hom m := by
  dsimp only
  let : Module (U.toScheme.presheaf.stalk x) (N.presheaf.stalk x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := U.toScheme.presheaf) N.val x
  let : Module (X.presheaf.stalk x.1) (M.presheaf.stalk x.1) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) M.val x.1
  let F : N.presheaf.stalk x ⟶ M.presheaf.stalk x.1 :=
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
    ((Scheme.Modules.toPresheaf _).map φ) ≫
      (Scheme.Modules.restrictStalkNatIso U.ι x).hom.app M
  have hg (W : U.toScheme.Opens) (hxW : x ∈ W) (b : Γ(N, W)) :
      F.hom ((N.presheaf.germ W x hxW).hom b) =
        (M.presheaf.germ (U.ι ''ᵁ W) x.1 ⟨x, hxW, rfl⟩).hom (φ.app W b) :=
    Modules.germ_stalkMap_restrictStalkNatIso U.ι M N φ x W hxW b
  -- With the two germ formulas available as closed equations, the scalar action on a stalk
  -- is computed on a common open on which both arguments are germs of sections.
  have key (W : U.toScheme.Opens) (hxW : x ∈ W) (c : Γ(U.toScheme, W)) (b : Γ(N, W)) :
      F.hom ((U.toScheme.presheaf.germ W x hxW).hom c • (N.presheaf.germ W x hxW).hom b) =
        (U.stalkIso x).hom.hom ((U.toScheme.presheaf.germ W x hxW).hom c) •
          F.hom ((N.presheaf.germ W x hxW).hom b) := by
    -- `φ` is `𝒪_U`-linear, and the scalar action on its value is the one on `Γ(M, U.ι ''ᵁ W)`.
    have happ : (φ.app W (c • b) : Γ(M, U.ι ''ᵁ W)) =
        @HSMul.hSMul Γ(X, U.ι ''ᵁ W) Γ(M, U.ι ''ᵁ W) Γ(M, U.ι ''ᵁ W) _ c (φ.app W b) :=
      (Scheme.Modules.Hom.app_smul φ c b).trans
        (Modules.smul_restrict_ι U M W c (φ.app W b))
    have hstalk : (X.presheaf.germ (U.ι ''ᵁ W) x.1 ⟨x, hxW, rfl⟩).hom c =
        (U.stalkIso x).hom.hom ((U.toScheme.presheaf.germ W x hxW).hom c) :=
      (ConcreteCategory.congr_hom (U.germ_stalkIso_hom x hxW) c).symm
    exact (congrArg F.hom (Modules.germ_smul N x W hxW c b).symm).trans
      ((hg W hxW (c • b)).trans
        ((congrArg (M.presheaf.germ (U.ι ''ᵁ W) x.1 ⟨x, hxW, rfl⟩).hom happ).trans
          ((Modules.germ_smul M x.1 (U.ι ''ᵁ W) ⟨x, hxW, rfl⟩ c (φ.app W b)).trans
            ((congrArg (fun t => t •
                (M.presheaf.germ (U.ι ''ᵁ W) x.1 ⟨x, hxW, rfl⟩).hom
                  (φ.app W b : Γ(M, U.ι ''ᵁ W))) hstalk).trans
              (congrArg (fun t => (U.stalkIso x).hom.hom
                ((U.toScheme.presheaf.germ W x hxW).hom c) • t) (hg W hxW b).symm)))))
  change F.hom (r • m) = (U.stalkIso x).hom.hom r • F.hom m
  obtain ⟨W₁, hx₁, a, ha₀⟩ := U.toScheme.presheaf.exists_germ_eq r
  obtain ⟨W₂, hx₂, b, hb₀⟩ := N.presheaf.exists_germ_eq m
  rw [← ha₀, ← hb₀]
  let W := W₁ ⊓ W₂
  have hxW : x ∈ W := ⟨hx₁, hx₂⟩
  let a' := (U.toScheme.presheaf.map (homOfLE (show W ≤ W₁ from inf_le_left)).op).hom a
  let b' := (N.presheaf.map (homOfLE (show W ≤ W₂ from inf_le_right)).op).hom b
  have ha : (U.toScheme.presheaf.germ W x hxW).hom a' =
      (U.toScheme.presheaf.germ W₁ x hx₁).hom a :=
    U.toScheme.presheaf.germ_res_apply _ _ _ _
  have hb : (N.presheaf.germ W x hxW).hom b' =
      (N.presheaf.germ W₂ x hx₂).hom b := N.presheaf.germ_res_apply _ _ _ _
  change F.hom _ = _ • F.hom _
  rw [← ha, ← hb]
  exact key W hxW a' b'

private theorem HasNonzeroRelativeDifferential.resLE
    {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens) (V : S.Opens)
    (e : U ≤ f ⁻¹ᵁ V) (x : U.toScheme) (h : X.presheaf.stalk x.1)
    (hdh : HasNonzeroRelativeDifferential f x.1 h) :
    HasNonzeroRelativeDifferential (f.resLE V U e) x ((U.stalkIso x).inv.hom h) := by
  let g := f.resLE V U e
  let M := Scheme.Hom.relativeDifferentials f
  let N := Scheme.Hom.relativeDifferentials g
  obtain ⟨i, hi, -⟩ := Scheme.Hom.relativeDifferentials_restrict f U V e
  let F : N.presheaf.stalk x ⟶ M.presheaf.stalk x.1 :=
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
    ((Scheme.Modules.toPresheaf _).map i.inv) ≫
      (Scheme.Modules.restrictStalkNatIso U.ι x).hom.app M
  let := SmoothAtJacobian.relativeDifferentialStalkModule f x.1
  let := SmoothAtJacobian.relativeDifferentialStalkModule g x
  let L : SmoothAtJacobian.relativeDifferentialStalk g x →ₛₗ[(U.stalkIso x).hom.hom]
      SmoothAtJacobian.relativeDifferentialStalk f x.1 :=
    { F.hom with map_smul' := restrict_stalkMap_smul U M N i.inv x }
  let : Algebra (X.presheaf.stalk x.1) (X.residueField x.1) := (X.residue x.1).hom.toAlgebra
  let : Algebra (U.toScheme.presheaf.stalk x) (U.toScheme.residueField x) :=
    (U.toScheme.residue x).hom.toAlgebra
  let K : U.toScheme.residueField x →ₛₗ[(U.stalkIso x).hom.hom] X.residueField x.1 :=
    { (IsLocalRing.ResidueField.map (U.stalkIso x).hom.hom).toAddMonoidHom with
      map_smul' := by
        intro r k
        change IsLocalRing.ResidueField (U.toScheme.presheaf.stalk x) at k
        change IsLocalRing.ResidueField.map _ (IsLocalRing.residue _ r * k) =
          IsLocalRing.residue _ ((U.stalkIso x).hom.hom r) *
            IsLocalRing.ResidueField.map (U.stalkIso x).hom.hom k
        rw [map_mul, IsLocalRing.ResidueField.map_residue] }
  have hdh₀ := hdh
  obtain ⟨W, hxW, a, ha, -⟩ := hdh
  let T := U.ι ⁻¹ᵁ W
  have hxT : x ∈ T := hxW
  let b := (U.ι.app W).hom a
  have hb : (U.toScheme.presheaf.germ T x hxT).hom b = (U.stalkIso x).inv.hom h :=
    ((ConcreteCategory.congr_hom (U.ι.germ_stalkMap W x hxW) a).symm.trans
        (congrArg (U.ι.stalkMap x).hom ha)).trans
      (ConcreteCategory.congr_hom (Scheme.Opens.stalkIso_inv U x) h).symm
  refine ⟨T, hxT, b, hb, ?_⟩
  change (1 : U.toScheme.residueField x) ⊗ₜ[U.toScheme.presheaf.stalk x]
    (N.presheaf.germ T x hxT).hom ((Scheme.Hom.universalRelativeDerivation g).d b) ≠ 0
  intro hz
  have hz' := congrArg (TensorProduct.map K L) hz
  rw [TensorProduct.map_tmul, map_zero] at hz'
  have hK : K 1 = 1 := map_one (IsLocalRing.ResidueField.map (U.stalkIso x).hom.hom)
  rw [hK] at hz'
  have hL : L ((N.presheaf.germ T x hxT).hom
        ((Scheme.Hom.universalRelativeDerivation g).d b)) =
      (M.presheaf.germ (U.ι ''ᵁ T) x.1 ⟨x, hxT, rfl⟩).hom
        ((Scheme.Hom.universalRelativeDerivation f).d b) := by
    have hid := hi T b
    simp only [Scheme.Opens.ι_appIso, Iso.refl_inv] at hid
    have hinv : (i.inv.val.app (.op T)).hom
        ((Scheme.Hom.universalRelativeDerivation g).d b) =
          (Scheme.Hom.universalRelativeDerivation f).d b := by
      change (i.hom.val.app (.op T)).hom
        ((Scheme.Hom.universalRelativeDerivation f).d b) =
          (Scheme.Hom.universalRelativeDerivation g).d b at hid
      rw [← hid]
      change ((i.hom ≫ i.inv).val.app (.op T)).hom _ = _
      rw [i.hom_inv_id]
      rfl
    change F.hom ((N.presheaf.germ T x hxT).hom
      ((Scheme.Hom.universalRelativeDerivation g).d b)) = _
    exact (Modules.germ_stalkMap_restrictStalkNatIso U.ι M N i.inv x T hxT
        ((Scheme.Hom.universalRelativeDerivation g).d b)).trans
      (congrArg (M.presheaf.germ (U.ι ''ᵁ T) x.1 ⟨x, hxT, rfl⟩).hom hinv)
  rw [hL] at hz'
  have hb' : (X.presheaf.germ (U.ι ''ᵁ T) x.1 ⟨x, hxT, rfl⟩).hom b = h := by
    have he := ConcreteCategory.congr_hom (U.germ_stalkIso_hom x hxT) b
    change (U.stalkIso x).hom.hom ((U.toScheme.presheaf.germ T x hxT).hom b) = _ at he
    rw [hb] at he
    exact he.symm.trans (ConcreteCategory.congr_hom (U.stalkIso x).inv_hom_id h)
  exact (HasNonzeroRelativeDifferential.ne_zero_of_germ_eq
    hdh₀ (U.ι ''ᵁ T) ⟨x, hxT, rfl⟩ b hb') hz'

@[ega "IV 17.5.8" "(iii), special case", sga "1 II 3.1" "special case"]
private theorem regularLocalRing_of_smoothAt_over_field
    {k : Type u} [Field k] {Z : Scheme.{u}}
    (g : Z ⟶ Spec (.of k)) (z : Z) (hz : InfinitesimalLifting.SmoothAt g z) :
    IsRegularLocalRing (Z.presheaf.stalk z) := by
  obtain ⟨U, V, hU, hV, hzU, hUV, hs⟩ :=
    (InfinitesimalLifting.smoothAt_iff_exists_affine g z).mp hz
  obtain rfl : V = ⊤ := top_unique fun y _ => Subsingleton.elim (g z) y ▸ hUV hzU
  let C := Γ(Spec (.of k), ⊤)
  let B := Γ(Z, U)
  let : Field C :=
    ((Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.isField
      (Field.toIsField k)).toField
  let : Algebra C B := (g.appLE ⊤ U hUV).hom.toAlgebra
  have : Algebra.Smooth C B := hs
  let xU : U.toScheme := ⟨z, hzU⟩
  let q : PrimeSpectrum B := hU.primeIdealOf xU
  let A := Z.presheaf.stalk z
  let : Algebra B A := Z.presheaf.algebra_section_stalk xU
  have : IsLocalization.AtPrime A q.asIdeal := hU.isLocalization_stalk xU
  exact (Algebra.isSmoothAt_tfae_localKrullDim_and_isRegularLocalRing q A).2
    (inferInstance : Algebra.IsSmoothAt C q.asIdeal)

@[ega "IV 17.5.8" "(iii), special case", sga "1 II 3.1" "special case"]
private theorem regularLocalRing_of_smooth_over_field
    {k : Type u} [Field k] {Z : Scheme.{u}}
    (g : Z ⟶ Spec (.of k)) [Smooth g] (z : Z) :
    IsRegularLocalRing (Z.presheaf.stalk z) := by
  have hstalk : (g.stalkMap z).hom.FormallySmooth := by
    rw [← Scheme.Hom.mem_smoothLocus, g.smoothLocus_eq_top]
    trivial
  obtain ⟨V, hV, U, hU, hVU, hzU, hsmooth⟩ :=
    AlgebraicGeometry.exists_smooth_of_formallySmooth_stalk g z hstalk
  obtain rfl : V = ⊤ := top_unique fun y _ => Subsingleton.elim (g z) y ▸ hVU hzU
  let C := Γ(Spec (.of k), ⊤)
  let B := Γ(Z, U)
  let : Field C :=
    ((Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.isField
      (Field.toIsField k)).toField
  let : Algebra C B := (g.appLE ⊤ U hVU).hom.toAlgebra
  have : Algebra.FinitePresentation C B :=
    g.finitePresentation_appLE (isAffineOpen_top (Spec (.of k))) hU hVU
  have : Algebra.FiniteType C B := inferInstance
  let xU : U.toScheme := ⟨z, hzU⟩
  let qP : PrimeSpectrum B := hU.primeIdealOf xU
  let q : Ideal B := qP.asIdeal
  let A := Z.presheaf.stalk z
  let : Algebra B A := TopCat.Presheaf.algebra_section_stalk Z.presheaf xU
  have : IsLocalization.AtPrime A q := hU.isLocalization_stalk xU
  have hqsm : Algebra.IsSmoothAt C q := by
    change qP ∈ Algebra.smoothLocus C B
    exact (AlgebraicGeometry.formallySmooth_stalkMap_iff ⊤
      (isAffineOpen_top (Spec (.of k)))
      U hU hVU hzU).mp hstalk
  exact (Algebra.isSmoothAt_tfae_localKrullDim_and_isRegularLocalRing qP A).2 hqsm

private theorem germ_eq_transport {X : Scheme.{u}} (W : X.Opens) {x y : X}
    (e : x = y) (hx : x ∈ W) (hy : y ∈ W) (a : Γ(X, W)) :
    (X.presheaf.germ W x hx).hom a = e.symm ▸ (X.presheaf.germ W y hy).hom a := by
  subst y
  rfl

private theorem fiber_regular_of_nonzero_differential
    {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] (x : X)
    (h : X.presheaf.stalk x) (hdh : HasNonzeroRelativeDifferential f x h) :
    IsRegular (((f.fiberι (f x)).stalkMap (f.asFiber x)).hom
      ((f.fiberι_asFiber x).symm ▸ h)) := by
  obtain ⟨W, hxW, a, ha, hxIW, hne, -⟩ :=
    fiberImage_ne_zero_of_hasNonzeroRelativeDifferential f x h hdh
  have hsmooth : Smooth (f.fiberToSpecResidueField (f x)) := by
    change Smooth (CategoryTheory.Limits.pullback.snd f (S.fromSpecResidueField (f x)))
    infer_instance
  -- The fibre over the residue field is a scheme over `Spec (CommRingCat.of κ(f x))`, a
  -- spelling of its base that instance search does not reach from `hsmooth`'s, so the
  -- smoothness hypothesis is handed over explicitly.
  have : IsRegularLocalRing ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) :=
    @regularLocalRing_of_smooth_over_field _ _ _ (f.fiberToSpecResidueField (f x)) hsmooth
      (f.asFiber x)
  have : IsDomain ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) :=
    IsRegularLocalRing.isDomain _
  apply IsRegular.of_ne_zero
  subst h
  have hp := Scheme.Hom.asFiberHom_apply f x (IsLocalRing.closedPoint (X.residueField x))
  generalize (f.asFiberHom x) (IsLocalRing.closedPoint (X.residueField x)) = z at hxIW hne hp
  subst z
  have hg := germ_eq_transport W (f.fiberι_asFiber x) hxIW hxW a
  rwa [hg] at hne

private theorem germ_topIso
    {X : Scheme.{u}} (U : X.Opens) (x : X) (hx : x ∈ U)
    (a : Γ(U.toScheme, ⊤)) :
    (U.ι.stalkMap ⟨x, hx⟩).hom
      ((X.presheaf.germ U x hx).hom (U.topIso.hom.hom a)) =
        U.toScheme.presheaf.germ ⊤ ⟨x, hx⟩ (by trivial) a := by
  have happ : U.ι.appLE U ⊤ U.ι_preimage_self.ge = U.topIso.inv := by
    simp only [Scheme.Hom.appLE, Scheme.Opens.ι_app_self, Scheme.Opens.topIso_inv]
    exact (X.presheaf.map_comp _ _).symm.trans
      (congrArg X.presheaf.map (Subsingleton.elim _ _))
  have hg : X.presheaf.germ U x hx ≫ U.ι.stalkMap ⟨x, hx⟩ =
      U.topIso.inv ≫ U.toScheme.presheaf.germ ⊤ ⟨x, hx⟩ (by trivial) := by
    rw [← happ, Scheme.Hom.appLE, Category.assoc]
    exact (Scheme.Hom.germ_stalkMap U.ι U ⟨x, hx⟩ hx).trans
      (congrArg (fun k => U.ι.app U ≫ k)
        (TopCat.Presheaf.germ_res U.toScheme.presheaf
          (homOfLE U.ι_preimage_self.ge) (⟨x, hx⟩ : U.toScheme) (by trivial)).symm)
  have hh := ConcreteCategory.congr_hom hg (U.topIso.hom.hom a)
  change (U.ι.stalkMap ⟨x, hx⟩).hom ((X.presheaf.germ U x hx).hom (U.topIso.hom.hom a)) =
    (U.toScheme.presheaf.germ ⊤ ⟨x, hx⟩ (by trivial)).hom
      (U.topIso.inv.hom (U.topIso.hom.hom a)) at hh
  have he : U.topIso.inv.hom (U.topIso.hom.hom a) = a :=
    ConcreteCategory.congr_hom U.topIso.hom_inv_id a
  exact hh.trans (congrArg (U.toScheme.presheaf.germ ⊤ ⟨x, hx⟩ (by trivial)).hom he)

private theorem exists_affine_effectiveCartierDivisor_flat_of_nonzero_differential
    {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] (x : X)
    (h : X.presheaf.stalk x)
    (hh : h ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (hdh : HasNonzeroRelativeDifferential f x h) :
    ∃ (U : X.Opens) (_hU : IsAffineOpen U) (hxU : x ∈ U)
      (a : Γ(X, U)) (I : U.toScheme.IdealSheafData),
      ((TopCat.Presheaf.germ X.presheaf U x hxU).hom a = h) ∧
      (∀ V : U.toScheme.affineOpens,
        I.ideal V = Ideal.span
          {((U.toScheme.presheaf.map (homOfLE le_top).op).hom
            (U.topIso.inv.hom a))}) ∧
      Stacks.Divisors.IsEffectiveCartierDivisor I ∧
      (⟨x, hxU⟩ : U.toScheme) ∈ I.support ∧
      Flat (I.subschemeι ≫ U.ι ≫ f) ∧
      LocallyOfFinitePresentation (I.subschemeι ≫ U.ι ≫ f) := by
  obtain ⟨U, hx, a, ha, hsupp, hI, hflat, hfp⟩ :=
    Stacks.AlgebraicGeometry.exists_affineOpen_effectiveCartierDivisor_of_isRegular_fiber f x h hh
      (by exact Flat.stalkMap f x)
      (fiber_regular_of_nonzero_differential f x h hdh)
  refine ⟨U.1, U.2, hx, U.1.topIso.hom.hom a,
    Scheme.IdealSheafData.ofIdealTop (Ideal.span {a}), ?_, ?_, hI, hsupp, hflat, hfp⟩
  · apply ((U.1.stalkIso ⟨x, hx⟩).symm.commRingCatIsoToRingEquiv.injective)
    change (U.1.stalkIso ⟨x, hx⟩).inv.hom _ = (U.1.stalkIso ⟨x, hx⟩).inv.hom h
    rw [Scheme.Opens.stalkIso_inv]
    exact (germ_topIso U.1 x hx a).trans ha.symm
  · intro V
    have he : U.1.topIso.inv.hom (U.1.topIso.hom.hom a) = a :=
      ConcreteCategory.congr_hom U.1.topIso.hom_inv_id a
    rw [he]
    simp only [Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_span, Set.image_singleton]

private theorem formallySmooth_stalkMap_principal_subscheme
    {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] (U₀ : X.affineOpens)
    (a₀ : Γ(X, U₀.1)) (I : U₀.1.toScheme.IdealSheafData)
    (hI : ∀ V : U₀.1.toScheme.affineOpens,
      I.ideal V = Ideal.span
        {((U₀.1.toScheme.presheaf.map (homOfLE le_top).op).hom
          (U₀.1.topIso.inv.hom a₀))}) (z : I.subscheme)
    (hdh : HasNonzeroRelativeDifferential f (U₀.1.ι (I.subschemeι z))
      ((X.presheaf.germ U₀.1 _ (I.subschemeι z).2).hom a₀)) :
    ((I.subschemeι ≫ U₀.1.ι ≫ f).stalkMap z).hom.FormallySmooth := by
  let x := U₀.1.ι (I.subschemeι z)
  obtain ⟨_, ⟨V, hV, rfl⟩, hsV, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  have hx : x ∈ U₀.1 ⊓ f ⁻¹ᵁ V := ⟨(I.subschemeι z).2, hsV⟩
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hsub⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx (U₀.1 ⊓ f ⁻¹ᵁ V).isOpen
  change X.Opens at U
  have hUU : U ≤ U₀.1 := fun y hy => (hsub hy).1
  have hUV : U ≤ f ⁻¹ᵁ V := fun y hy => (hsub hy).2
  let T := U₀.1.ι ⁻¹ᵁ U
  have hT : IsAffineOpen T := hU.preimage_of_isOpenImmersion U₀.1.ι
    (by simpa only [Scheme.Opens.opensRange_ι] using hUU)
  let j := I.subschemeι ≫ U₀.1.ι
  let a := (X.presheaf.map (homOfLE hUU).op).hom a₀
  have hrestrict : (U₀.1.ι.app U).hom a =
      (U₀.1.toScheme.presheaf.map (homOfLE (show T ≤ ⊤ from le_top)).op).hom
        (U₀.1.topIso.inv.hom a₀) := by
    have he : X.presheaf.map (homOfLE hUU).op ≫ U₀.1.ι.app U =
        U₀.1.topIso.inv ≫ U₀.1.toScheme.presheaf.map (homOfLE (show T ≤ ⊤ from le_top)).op := by
      simp only [Scheme.Opens.ι_app, Scheme.Opens.topIso_inv,
        Scheme.Opens.toScheme_presheaf_map]
      exact presheaf_map_comp_eq _ _ _ _
    exact ConcreteCategory.congr_hom he a₀
  have : IsIso (U₀.1.ι.app U) := U₀.1.ι.isIso_app U
    (by simpa only [Scheme.Opens.opensRange_ι] using hUU)
  have hi : Function.Surjective (j.app U) :=
    (I.subschemeι.app_surjective T hT).comp
      (ConcreteCategory.bijective_of_isIso (U₀.1.ι.app U)).2
  have hker : RingHom.ker (j.app U).hom = Ideal.span {a} := by
    change RingHom.ker ((I.subschemeι.app T).hom.comp (U₀.1.ι.app U).hom) = _
    rw [← RingHom.comap_ker, I.ker_subschemeι_app ⟨T, hT⟩, hI, ← hrestrict,
      ← Set.image_singleton, ← Ideal.map_span]
    exact Ideal.comap_map_of_bijective _
      (ConcreteCategory.bijective_of_isIso (U₀.1.ι.app U))
  have hda : HasNonzeroRelativeDifferential f (j z)
      ((X.presheaf.germ U (j z) hxU).hom a) := by
    have hg := X.presheaf.germ_res_apply (homOfLE hUU) (j z) hxU a₀
    change (X.presheaf.germ U (j z) hxU).hom a = _ at hg
    rwa [hg]
  have hsm := formallySmooth_stalkMap_of_principal_ker j f z
    ⟨U, hU⟩ ⟨V, hV⟩ hxU hUV (hT.preimage I.subschemeι) hi a hker hda
  change (((I.subschemeι ≫ U₀.1.ι) ≫ f).stalkMap z).hom.FormallySmooth at hsm
  rwa [Category.assoc] at hsm

private theorem exists_affineOpen_effectiveCartierDivisor_formallySmooth_stalk
    {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] (x : X)
    (h : X.presheaf.stalk x)
    (hh : h ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (hdh : HasNonzeroRelativeDifferential f x h) :
    ∃ (U : X.affineOpens) (hxU : x ∈ U.1)
      (a : Γ(X, U.1)) (I : U.1.toScheme.IdealSheafData),
      (X.presheaf.germ U.1 x hxU).hom a = h ∧
      (∀ V : U.1.toScheme.affineOpens,
        I.ideal V = Ideal.span
          {((U.1.toScheme.presheaf.map (homOfLE le_top).op).hom
            (U.1.topIso.inv.hom a))}) ∧
      Stacks.Divisors.IsEffectiveCartierDivisor I ∧
      LocallyOfFinitePresentation (I.subschemeι ≫ U.1.ι ≫ f) ∧
      ∃ z : I.subscheme, I.subschemeι z = (⟨x, hxU⟩ : U.1.toScheme) ∧
        ((I.subschemeι ≫ U.1.ι ≫ f).stalkMap z).hom.FormallySmooth := by
  obtain ⟨U, hU, hxU, a, I, ha, hIa, hI, hxI, hflat, hfp⟩ :=
    exists_affine_effectiveCartierDivisor_flat_of_nonzero_differential f x h hh hdh
  let z : I.subscheme := ⟨⟨x, hxU⟩, hxI⟩
  have hd : HasNonzeroRelativeDifferential f (U.ι (I.subschemeι z))
      ((X.presheaf.germ U _ (I.subschemeι z).2).hom a) := by
    change HasNonzeroRelativeDifferential f x ((X.presheaf.germ U x hxU).hom a)
    rwa [ha]
  have hsm := formallySmooth_stalkMap_principal_subscheme f ⟨U, hU⟩ a I hIa z hd
  exact ⟨⟨U, hU⟩, hxU, a, I, ha, hIa, hI, hfp, z, rfl, hsm⟩

/-- **The comparison of `V(I.comap f)` with `V(I)` composed with `V(I) ⟶ Y` is the pullback
square.** -/
private theorem comapIso_snd_comp_subschemeι {X Y : Scheme.{u}} (I : Y.IdealSheafData)
    (f : X ⟶ Y) :
    ((I.comapIso f).hom ≫ CategoryTheory.Limits.pullback.snd f I.subschemeι) ≫ I.subschemeι =
      (I.comap f).subschemeι ≫ f := by
  rw [Category.assoc, ← CategoryTheory.Limits.pullback.condition,
    ← Category.assoc, I.comapIso_hom_fst]

private theorem ideal_comap_eq_span {Y X : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] (I : X.IdealSheafData) (b : Γ(X, ⊤))
    (hb : ∀ V : X.affineOpens,
      I.ideal V = Ideal.span {(X.presheaf.map (homOfLE le_top).op).hom b})
    (V : Y.affineOpens) :
    (I.comap j).ideal V = Ideal.span
      {(Y.presheaf.map (homOfLE le_top).op).hom (j.appTop.hom b)} := by
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, hb]
  have hm := Ideal.map_comap_of_equiv
    (I := Ideal.span {(X.presheaf.map (homOfLE (show j ''ᵁ V.1 ≤ ⊤ from le_top)).op).hom b})
    (j.appIso V.1).commRingCatIsoToRingEquiv
  change Ideal.map (j.appIso V.1).hom.hom _ = Ideal.comap (j.appIso V.1).inv.hom _ at hm
  rw [← hm, Ideal.map_span, Set.image_singleton]
  congr 1
  congr 1
  have he : X.presheaf.map (homOfLE (show j ''ᵁ V.1 ≤ ⊤ from le_top)).op ≫
      (j.appIso V.1).hom = j.appTop ≫ Y.presheaf.map (homOfLE le_top).op := by
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]
    exact (appTop_comp_map j V.1).symm
  exact ConcreteCategory.congr_hom he b

private theorem exists_affineOpen_smooth_restriction_of_effectiveCartierDivisor
    {X S : Scheme.{u}} (f : X ⟶ S) (I : X.IdealSheafData)
    (hI : Stacks.Divisors.IsEffectiveCartierDivisor I)
    [LocallyOfFinitePresentation (I.subschemeι ≫ f)] (z : I.subscheme)
    (hz : ((I.subschemeι ≫ f).stalkMap z).hom.FormallySmooth) :
    ∃ (U : X.affineOpens) (_ : I.subschemeι z ∈ U.1),
      Stacks.Divisors.IsEffectiveCartierDivisor (I.comap U.1.ι) ∧
      Smooth ((I.comap U.1.ι).subschemeι ≫ U.1.ι ≫ f) := by
  let g := I.subschemeι ≫ f
  let W := g.smoothLocus
  have hzW : z ∈ W := hz
  have hclosed : IsClosed (I.subschemeι '' (W : Set I.subscheme)ᶜ) :=
    (IsClosedImmersion.isClosedEmbedding I.subschemeι).isClosedMap _ W.isOpen.isClosed_compl
  let O : X.Opens := ⟨(I.subschemeι '' (W : Set I.subscheme)ᶜ)ᶜ,
    hclosed.isOpen_compl⟩
  have hzO : I.subschemeι z ∈ O := by
    rintro ⟨y, hy, heq⟩
    exact hy ((IsClosedImmersion.isClosedEmbedding I.subschemeι).injective heq ▸ hzW)
  obtain ⟨_, ⟨U, hU, rfl⟩, hzU, hUO⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hzO O.isOpen
  change X.Opens at U
  let J := I.comap U.ι
  let e : J.subscheme ⟶ I.subscheme :=
    (I.comapIso U.ι).hom ≫ CategoryTheory.Limits.pullback.snd U.ι I.subschemeι
  have he : e ≫ I.subschemeι = J.subschemeι ≫ U.ι := comapIso_snd_comp_subschemeι I U.ι
  have : IsOpenImmersion e := inferInstance
  have heW : ∀ y : J.subscheme, e y ∈ W := by
    intro y
    by_contra hy
    have hUO' := hUO (J.subschemeι y).2
    apply hUO'
    refine ⟨e y, hy, ?_⟩
    exact congrArg (fun k : J.subscheme ⟶ X => k y) he
  have hsm : Smooth (e ≫ g) := by
    apply (Scheme.Hom.smoothLocus_eq_top_iff).mp
    rw [← Scheme.Hom.preimage_smoothLocus_eq e g]
    exact top_unique (fun y _ => heW y)
  have hsm' : Smooth (J.subschemeι ≫ U.ι ≫ f) := by
    have hcomp : e ≫ g = J.subschemeι ≫ U.ι ≫ f := by
      change e ≫ (I.subschemeι ≫ f) = _
      rw [← Category.assoc, he, Category.assoc]
    rwa [hcomp] at hsm
  exact ⟨⟨U, hU⟩, hzU,
    Stacks.Divisors.isPullbackDefined_of_flat U.ι I hI, hsm'⟩

private theorem exists_affineOpen_smooth_principal_restriction
    {X S : Scheme.{u}} (f : X ⟶ S) (I : X.IdealSheafData) (b : Γ(X, ⊤))
    (hb : ∀ V : X.affineOpens,
      I.ideal V = Ideal.span {(X.presheaf.map (homOfLE le_top).op).hom b})
    (hI : Stacks.Divisors.IsEffectiveCartierDivisor I)
    [LocallyOfFinitePresentation (I.subschemeι ≫ f)] (z : I.subscheme)
    (hz : ((I.subschemeι ≫ f).stalkMap z).hom.FormallySmooth) :
    ∃ (U : X.affineOpens) (hxU : I.subschemeι z ∈ U.1),
      let J := I.comap U.1.ι
      (∀ V : U.1.toScheme.affineOpens,
        J.ideal V = Ideal.span
          {(U.1.toScheme.presheaf.map (homOfLE le_top).op).hom (U.1.ι.appTop.hom b)}) ∧
      Stacks.Divisors.IsEffectiveCartierDivisor J ∧
      (⟨I.subschemeι z, hxU⟩ : U.1.toScheme) ∈ J.support ∧
      Smooth (J.subschemeι ≫ U.1.ι ≫ f) := by
  obtain ⟨U, hxU, hJU, hsm⟩ :=
    exists_affineOpen_smooth_restriction_of_effectiveCartierDivisor f I hI z hz
  refine ⟨U, hxU, fun V => ideal_comap_eq_span U.1.ι I b hb V, hJU, ?_, hsm⟩
  rw [Scheme.IdealSheafData.support_comap]
  change I.subschemeι z ∈ I.support
  exact (I.range_subschemeι).le ⟨z, rfl⟩

private theorem germ_appTop {Y X : Scheme.{u}} (j : Y ⟶ X) (y : Y) :
    j.appTop ≫ Y.presheaf.germ ⊤ y (by trivial) =
      X.presheaf.germ ⊤ (j y) (by trivial) ≫ j.stalkMap y :=
  (j.germ_stalkMap ⊤ y (by trivial)).symm

private theorem exists_smooth_slice_of_openImmersion
    {Y X S : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] [IsAffine Y]
    (f : X ⟶ S) (y : Y) (h : X.presheaf.stalk (j y)) (b : Γ(Y, ⊤))
    (I : Y.IdealSheafData)
    (hb : (j.stalkMap y).hom h = (Y.presheaf.germ ⊤ y (by trivial)).hom b)
    (hI : ∀ V : Y.affineOpens,
      I.ideal V = Ideal.span {(Y.presheaf.map (homOfLE le_top).op).hom b})
    (heff : Stacks.Divisors.IsEffectiveCartierDivisor I)
    (hy : y ∈ I.support) [Smooth (I.subschemeι ≫ j ≫ f)] :
    ∃ (U : X.Opens) (_hU : IsAffineOpen U) (hxU : j y ∈ U)
      (a : Γ(X, U)) (J : U.toScheme.IdealSheafData),
      (X.presheaf.germ U (j y) hxU).hom a = h ∧
      (∀ V : U.toScheme.affineOpens,
        J.ideal V = Ideal.span
          {(U.toScheme.presheaf.map (homOfLE le_top).op).hom (U.topIso.inv.hom a)}) ∧
      Stacks.Divisors.IsEffectiveCartierDivisor J ∧
      (⟨j y, hxU⟩ : U.toScheme) ∈ J.support ∧
      Smooth (J.subschemeι ≫ U.ι ≫ f) := by
  let U := j.opensRange
  let e := j.isoOpensRange
  have hU : IsAffineOpen U := by
    simpa only [Scheme.Hom.image_top_eq_opensRange] using
      (isAffineOpen_top Y).image_of_isOpenImmersion j
  have hxU : j y ∈ U := ⟨y, rfl⟩
  let x : U.toScheme := ⟨j y, hxU⟩
  have hex : e.inv x = y := j.isOpenEmbedding.injective
    (congrArg (fun k : U.toScheme ⟶ X => k x) j.isoOpensRange_inv_comp)
  let c := e.inv.appTop.hom b
  let a := U.topIso.hom.hom c
  let J := I.comap e.inv
  have hac : U.topIso.inv.hom a = c := ConcreteCategory.congr_hom U.topIso.hom_inv_id c
  have hxJ : x ∈ J.support := by
    rw [Scheme.IdealSheafData.support_comap]
    change e.inv x ∈ I.support
    rwa [hex]
  let k : J.subscheme ⟶ I.subscheme :=
    (I.comapIso e.inv).hom ≫ CategoryTheory.Limits.pullback.snd e.inv I.subschemeι
  have hk : k ≫ I.subschemeι = J.subschemeι ≫ e.inv := comapIso_snd_comp_subschemeι I e.inv
  have hkf : k ≫ (I.subschemeι ≫ j ≫ f) = J.subschemeι ≫ U.ι ≫ f := by
    rw [← Category.assoc k, hk, Category.assoc]
    exact congrArg (fun l => J.subschemeι ≫ l ≫ f) j.isoOpensRange_inv_comp
  have hsm : Smooth (J.subschemeι ≫ U.ι ≫ f) := by
    rw [← hkf]
    infer_instance
  refine ⟨U, hU, hxU, a, J, ?_, ?_,
    Stacks.Divisors.isPullbackDefined_of_flat e.inv I heff, hxJ, hsm⟩
  · apply (ConcreteCategory.bijective_of_isIso (U.ι.stalkMap x)).1
    change (U.ι.stalkMap x).hom _ = (U.ι.stalkMap x).hom h
    rw [germ_topIso U (j y) hxU c]
    have heh : (U.ι.stalkMap x).hom h =
        (U.toScheme.presheaf.germ ⊤ x (by trivial)).hom c := by
      obtain ⟨Q, hyQ, d, hd⟩ := X.presheaf.exists_germ_eq h
      have hbQ : (Y.presheaf.germ (j ⁻¹ᵁ Q) y hyQ).hom ((j.app Q).hom d) =
          (Y.presheaf.germ ⊤ y (by trivial)).hom b := by
        rw [← hd] at hb
        exact (ConcreteCategory.congr_hom (j.germ_stalkMap Q y hyQ) d).symm.trans hb
      have hzQ : (e.inv ≫ j) x ∈ Q := by
        change j (e.inv x) ∈ Q
        simpa only [hex] using hyQ
      have hbQ' : (Y.presheaf.germ (j ⁻¹ᵁ Q) (e.inv x) hzQ).hom ((j.app Q).hom d) =
          (Y.presheaf.germ ⊤ (e.inv x) (by trivial)).hom b := by
        have H : ∀ (p : Y), p = y → ∀ hp : j p ∈ Q,
            (Y.presheaf.germ (j ⁻¹ᵁ Q) p hp).hom ((j.app Q).hom d) =
              (Y.presheaf.germ ⊤ p (by trivial)).hom b := by
          rintro p rfl hp
          exact hbQ
        exact H _ hex hzQ
      have hc := ConcreteCategory.congr_hom (germ_appTop e.inv x) b
      change (U.toScheme.presheaf.germ ⊤ x (by trivial)).hom c =
        (e.inv.stalkMap x).hom ((Y.presheaf.germ ⊤ (e.inv x) (by trivial)).hom b) at hc
      have heq : (U.toScheme.presheaf.germ ⊤ x (by trivial)).hom c =
          ((e.inv ≫ j).stalkMap x).hom
            ((X.presheaf.germ Q ((e.inv ≫ j) x) hzQ).hom d) := by
        rw [Scheme.Hom.stalkMap_comp]
        change _ = (e.inv.stalkMap x).hom ((j.stalkMap (e.inv x)).hom _)
        rw [hc, ← hbQ']
        exact congrArg (e.inv.stalkMap x).hom
          (ConcreteCategory.congr_hom (j.germ_stalkMap Q (e.inv x) hzQ) d).symm
      have heq' : ∀ hp : (e.inv ≫ j) x ∈ Q,
          (U.toScheme.presheaf.germ ⊤ x (by trivial)).hom c =
            ((e.inv ≫ j).stalkMap x).hom
              ((X.presheaf.germ Q ((e.inv ≫ j) x) hp).hom d) := fun _ => heq
      rw [j.isoOpensRange_inv_comp] at heq'
      exact (congrArg (U.ι.stalkMap x).hom hd).symm.trans (heq' hyQ).symm
    exact heh.symm
  · intro V
    rw [hac]
    exact ideal_comap_eq_span e.inv I b hI V

/-- **Stacks Project, Tag 057C.** A local equation with nonzero relative
differential cuts out a smooth effective Cartier divisor near the point. -/
@[stacks 057C, sga "1 II 4.12" "dF(x)≠0 ⇒ Y smooth"]
public theorem exists_smooth_effectiveCartierDivisor_of_nonzero_differential
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (h : X.presheaf.stalk x)
    (hh : h ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (hf : InfinitesimalLifting.SmoothAt f x)
    (hdh : HasNonzeroRelativeDifferential f x h) :
    ∃ (U : X.Opens) (_hU : IsAffineOpen U) (hxU : x ∈ U)
      (a : Γ(X, U)) (I : U.toScheme.IdealSheafData),
      ((TopCat.Presheaf.germ X.presheaf U x hxU).hom a = h) ∧
      (∀ V : U.toScheme.affineOpens,
        I.ideal V = Ideal.span
          {((U.toScheme.presheaf.map (homOfLE le_top).op).hom
            (U.topIso.inv.hom a))}) ∧
      Stacks.Divisors.IsEffectiveCartierDivisor I ∧
      (⟨x, hxU⟩ : U.toScheme) ∈ I.support ∧
      Smooth (I.subschemeι ≫ U.ι ≫ f) := by
  obtain ⟨U₀, V₀, hU₀, hV₀, hx₀, hUV, hs⟩ :=
    (InfinitesimalLifting.smoothAt_iff_exists_affine f x).mp hf
  let g := f.resLE V₀ U₀ hUV
  have : IsAffine U₀.toScheme := hU₀
  have : IsAffine V₀.toScheme := hV₀
  have : Smooth g :=
    (HasRingHomProperty.iff_of_isAffine (P := @Smooth)).2
      ((RingHom.Smooth.propertyIsLocal.respectsIso.arrow_mk_iso_iff
        (arrowResLEAppIso f V₀ U₀ hUV)).mpr hs)
  let x₀ : U₀.toScheme := ⟨x, hx₀⟩
  let h₀ := (U₀.stalkIso x₀).inv.hom h
  have hh₀ : h₀ ∈ IsLocalRing.maximalIdeal (U₀.toScheme.presheaf.stalk x₀) :=
    map_nonunit (U₀.stalkIso x₀).inv.hom h hh
  have hdh₀ : HasNonzeroRelativeDifferential g x₀ h₀ :=
    HasNonzeroRelativeDifferential.resLE f U₀ V₀ hUV x₀ h hdh
  obtain ⟨T, hxT, a, I, ha, hIa, heff, hfp, z, hz, hsm⟩ :=
    exists_affineOpen_effectiveCartierDivisor_formallySmooth_stalk g x₀ h₀ hh₀ hdh₀
  let b := T.1.topIso.inv.hom a
  have : LocallyOfFinitePresentation (I.subschemeι ≫ (T.1.ι ≫ g)) := hfp
  obtain ⟨W, hxW, hJW, hJeff, hJpoint, hJsmooth⟩ :=
    exists_affineOpen_smooth_principal_restriction (T.1.ι ≫ g) I b hIa heff z hsm
  let J := I.comap W.1.ι
  have hxW' : (⟨x₀, hxT⟩ : T.1.toScheme) ∈ W.1 := hz ▸ hxW
  let y : W.1.toScheme := ⟨⟨x₀, hxT⟩, hxW'⟩
  let j := W.1.ι ≫ T.1.ι ≫ U₀.ι
  let c := W.1.ι.appTop.hom b
  have : IsAffine W.1.toScheme := W.2
  have : Smooth (J.subschemeι ≫ j ≫ f) := by
    have hcomp : J.subschemeι ≫ j ≫ f =
        (J.subschemeι ≫ W.1.ι ≫ T.1.ι ≫ g) ≫ V₀.ι := by
      dsimp only [j, g]
      simp only [Category.assoc, Scheme.Hom.resLE_comp_ι]
    rw [hcomp]
    have : Smooth (J.subschemeι ≫ W.1.ι ≫ T.1.ι ≫ g) := hJsmooth
    infer_instance
  have hyeq : y = (⟨I.subschemeι z, hxW⟩ : W.1.toScheme) := Subtype.ext hz.symm
  have hyJ : y ∈ J.support := hyeq ▸ hJpoint
  have hb : (T.1.ι.stalkMap (⟨x₀, hxT⟩ : T.1.toScheme)).hom h₀ =
      (T.1.toScheme.presheaf.germ ⊤ ⟨x₀, hxT⟩ (by trivial)).hom b := by
    have ht := germ_topIso T.1 x₀ hxT b
    have hab : T.1.topIso.hom.hom b = a :=
      ConcreteCategory.congr_hom T.1.topIso.inv_hom_id a
    rw [hab, ha] at ht
    exact ht
  have hc : (j.stalkMap y).hom h =
      (W.1.toScheme.presheaf.germ ⊤ y (by trivial)).hom c := by
    dsimp only [j]
    rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp]
    change (W.1.ι.stalkMap y).hom
      ((T.1.ι.stalkMap (⟨x₀, hxT⟩ : T.1.toScheme)).hom
        ((U₀.ι.stalkMap x₀).hom h)) = _
    rw [← Scheme.Opens.stalkIso_inv U₀ x₀]
    change (W.1.ι.stalkMap y).hom
      ((T.1.ι.stalkMap (⟨x₀, hxT⟩ : T.1.toScheme)).hom h₀) = _
    rw [hb]
    exact (ConcreteCategory.congr_hom (germ_appTop W.1.ι y) b).symm
  exact exists_smooth_slice_of_openImmersion j f y h c J hc hJW hJeff hyJ

end Stacks.AlgebraicGeometry

end
