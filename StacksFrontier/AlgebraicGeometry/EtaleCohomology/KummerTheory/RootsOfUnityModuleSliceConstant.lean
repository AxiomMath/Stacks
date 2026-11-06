module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.ConstantRootsOfUnity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.RootsOfUnityConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.RootsOfUnityModule

/-!
# `μ_N` is constant on an étale `X`-scheme carrying a primitive `N`-th root of unity

Let `X` be a scheme, `V` an étale `X`-scheme, `k` a field with a ring map `κ : k → Γ(V, 𝒪_V)`,
and `ζ ∈ k` a primitive `N`-th root of unity. Restricted to the slice site of `X_étale` at `V`,
the sheaf `μ_N` of `ℤ/N`-modules (`Stacks.Kummer.rootsOfUnityModule`) is the constant sheaf
`ℤ/N`, by `m ↦ ζ^m`; this is the slice-site form of `Stacks.Kummer.rootsOfUnityConstantIso`. The
map is injective because `ζ^m = 1` in a nonzero `k`-algebra forces `N ∣ m`. It is locally
surjective by the Lagrange idempotents attached to a root of unity.

## Main definitions

* `Stacks.Kummer.sliceRootSection`: the section `ζ^m` of `μ_N` over an object of the slice.
* `Stacks.Kummer.sliceRootPresheafHom`: `m ↦ ζ^m`, from the constant presheaf `ℤ/N` on the slice.
* `Stacks.Kummer.sliceRootSheafHom`: the induced morphism out of the constant sheaf.

## Main results

* `Stacks.Kummer.isIso_sliceRootSheafHom`: it is an isomorphism.
* `Stacks.Kummer.isConstant_overPullback_rootsOfUnityModule`: `μ_N` restricted to `V` is constant.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v

namespace Stacks.Kummer

variable {X : Scheme.{u}} (V : X.Etale) {k : Type u} [Field k] (κ : k →+* Γ(V.left, ⊤))
  {N : ℕ} [NeZero N] {ζ : k} (hζ : IsPrimitiveRoot ζ N)

/-- A root of unity `x` with `x ^ N = 1` satisfies `x ^ m = x ^ (m % N)`. -/
theorem pow_eq_pow_mod_of_pow_eq_one {M : Type*} [Monoid M] {x : M} {n : ℕ} (hx : x ^ n = 1)
    (m : ℕ) : x ^ m = x ^ (m % n) := by
  conv_lhs => rw [← Nat.mod_add_div m n, pow_add, pow_mul, hx, one_pow, mul_one]

/-- The structure map `k → Γ(W, 𝒪)` of an object `W` of the slice at `V`. -/
def sliceStructMap (W : Over V) : k →+* Γ(W.left.left, ⊤) :=
  W.hom.left.appTop.hom.comp κ

/-- The structure maps of the objects of the slice at `V` are compatible with its morphisms. -/
theorem sliceStructMap_comp {W W' : Over V} (g : W' ⟶ W) :
    g.left.left.appTop.hom.comp (sliceStructMap V κ W) = sliceStructMap V κ W' := by
  have h : g.left.left ≫ W.hom.left = W'.hom.left :=
    congrArg (fun h : W'.left ⟶ V => h.left) (Over.w g)
  rw [sliceStructMap, sliceStructMap, ← RingHom.comp_assoc, ← CommRingCat.hom_comp,
    ← Scheme.Hom.comp_appTop, h]

/-- The image of `ζ` in the invertible functions on an object of the slice. -/
def sliceRootOn (W : Over V) : (Γ(W.left.left, ⊤))ˣ :=
  Units.map (sliceStructMap V κ W).toMonoidHom (Units.mk0 ζ (hζ.ne_zero (NeZero.ne N)))

/-- The image of `ζ` on an object of the slice is an `N`-th root of unity. -/
theorem sliceRootOn_pow (W : Over V) : sliceRootOn V κ hζ W ^ N = 1 := by
  rw [sliceRootOn, ← map_pow, show Units.mk0 ζ (hζ.ne_zero (NeZero.ne N)) ^ N = 1 from
    Units.ext (by simpa using hζ.pow_eq_one), map_one]

/-- The image of `ζ` is compatible with restriction along a morphism of the slice. -/
theorem map_sliceRootOn {W W' : Over V} (g : W' ⟶ W) :
    Units.map g.left.left.appTop.hom (sliceRootOn V κ hζ W) = sliceRootOn V κ hζ W' := by
  rw [sliceRootOn, sliceRootOn, ← sliceStructMap_comp V κ g]
  rfl

/-- `ofUnit` turns products into sums. -/
theorem ofUnit_mul {U : X.Etale} (x y : (Γ(U.left, ⊤))ˣ) :
    ofUnit.{u, v} (x * y) = ofUnit x + ofUnit y :=
  rfl

/-- **The section `ζ^m` of `μ_N`** over an object of the slice at `V`. -/
def sliceRootSection (W : Over V) (m : ZMod N) :
    ToType ((rootsOfUnitySheaf.{u, v} X N).obj.obj (op W.left)) :=
  (rootsOfUnitySectionsEquiv.{u, v} X N (op W.left)).symm
    ⟨sliceRootOn V κ hζ W ^ m.val, by
      rw [← pow_mul, mul_comm, pow_mul, sliceRootOn_pow, one_pow]⟩

/-- The section `ζ^m` goes to the invertible function `ζ^m` in `𝐆_m`. -/
theorem rootsOfUnityι_sliceRootSection (W : Over V) (m : ZMod N) :
    (rootsOfUnityι.{u, v} X N).hom.app (op W.left) (sliceRootSection.{u, v} V κ hζ W m) =
      ofUnit (sliceRootOn V κ hζ W ^ m.val) := by
  calc (rootsOfUnityι.{u, v} X N).hom.app (op W.left) (sliceRootSection.{u, v} V κ hζ W m)
      = ofUnit.{u, v} (rootsOfUnitySection.{u, v} X N (op W.left)
          (sliceRootSection.{u, v} V κ hζ W m)).1 := rfl
    _ = ofUnit (sliceRootOn V κ hζ W ^ m.val) := by
      rw [← rootsOfUnitySectionsEquiv_apply, sliceRootSection, Equiv.apply_symm_apply]

/-- `m ↦ ζ^m` is additive. -/
theorem sliceRootSection_add (W : Over V) (a b : ZMod N) :
    sliceRootSection.{u, v} V κ hζ W (a + b) =
      sliceRootSection.{u, v} V κ hζ W a + sliceRootSection.{u, v} V κ hζ W b := by
  apply rootsOfUnityι_app_injective.{u, v} N W.left
  rw [map_add, rootsOfUnityι_sliceRootSection, rootsOfUnityι_sliceRootSection,
    rootsOfUnityι_sliceRootSection, ← ofUnit_mul, ← pow_add, ZMod.val_add,
    ← pow_eq_pow_mod_of_pow_eq_one (sliceRootOn_pow V κ hζ W)]

/-- `m ↦ ζ^m` commutes with multiplication by a natural number. -/
theorem sliceRootSection_nsmul (W : Over V) (c : ℕ) (a : ZMod N) :
    sliceRootSection.{u, v} V κ hζ W (c • a) = c • sliceRootSection.{u, v} V κ hζ W a := by
  induction c with
  | zero =>
    rw [zero_nsmul, zero_nsmul]
    apply rootsOfUnityι_app_injective.{u, v} N W.left
    rw [map_zero, rootsOfUnityι_sliceRootSection, ZMod.val_zero, pow_zero]
    rfl
  | succ c ih => rw [succ_nsmul, succ_nsmul, sliceRootSection_add, ih]

/-- The sections `ζ^m` are compatible with restriction along a morphism of the slice. -/
theorem sliceRootSection_naturality {W W' : Over V} (g : W' ⟶ W) (m : ZMod N) :
    (rootsOfUnitySheaf.{u, v} X N).obj.map g.left.op (sliceRootSection.{u, v} V κ hζ W m) =
      sliceRootSection.{u, v} V κ hζ W' m := by
  apply rootsOfUnityι_app_injective.{u, v} N W'.left
  rw [rootsOfUnityι_sliceRootSection, NatTrans.naturality_apply,
    rootsOfUnityι_sliceRootSection, map_ofUnit, map_pow, map_sliceRootOn]

variable (X) in
/-- Multiplication by `m` on a morphism of abelian sheaves, on sections. -/
theorem sheaf_nsmul_hom_app_apply
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}} (g : F ⟶ G) (m : ℕ)
    (U : (X.Etale)ᵒᵖ) (t : ToType (F.obj.obj U)) : (m • g).hom.app U t = m • g.hom.app U t := by
  induction m with
  | zero => rw [zero_nsmul, zero_nsmul]; rfl
  | succ m ih =>
    rw [succ_nsmul, succ_nsmul, ← ih]
    rfl

/-- The scalar action of `ℤ/N` on the sections of `μ_N` is through `ZMod.val`. -/
theorem rootsOfUnityModule_smul (U : (X.Etale)ᵒᵖ) (a : ZMod N)
    (s : ToType ((rootsOfUnityModule.{u, v} X N).obj.obj U)) :
    a • s = (a.val • s : ToType ((rootsOfUnitySheaf.{u, v} X N).obj.obj U)) :=
  sheaf_nsmul_hom_app_apply X (𝟙 (rootsOfUnitySheaf.{u, v} X N)) a.val U s

variable (N) in
/-- The constant presheaf `ℤ/N` of modules on the slice at `V`. -/
abbrev sliceConstantPresheaf : (Over V)ᵒᵖ ⥤ ModuleCat.{max (u + 1) v} (ZMod N) :=
  (Functor.const (Over V)ᵒᵖ).obj (ModuleCat.of (ZMod N) (ULift.{max (u + 1) v} (ZMod N)))

/-- **`m ↦ ζ^m`**, from the constant presheaf `ℤ/N` to `μ_N` restricted to the slice at `V`. -/
def sliceRootPresheafHom :
    sliceConstantPresheaf V N ⟶
      ((X.smallEtaleTopology.overPullback (ModuleCat.{max (u + 1) v} (ZMod N)) V).obj
        (rootsOfUnityModule.{u, v} X N)).obj where
  app W := ModuleCat.ofHom (X := ModuleCat.of (ZMod N) (ULift.{max (u + 1) v} (ZMod N)))
    (Y := ((X.smallEtaleTopology.overPullback (ModuleCat.{max (u + 1) v} (ZMod N)) V).obj
        (rootsOfUnityModule.{u, v} X N)).obj.obj W)
    { toFun := fun m => sliceRootSection.{u, v} V κ hζ W.unop m.down
      map_add' := fun a b => sliceRootSection_add V κ hζ W.unop a.down b.down
      map_smul' := fun a m => by
        have h1 : a * m.down = a.val • m.down := by
          rw [nsmul_eq_mul, ZMod.natCast_zmod_val]
        exact (congrArg (sliceRootSection.{u, v} V κ hζ W.unop) h1).trans
          ((sliceRootSection_nsmul V κ hζ W.unop a.val m.down).trans
            (rootsOfUnityModule_smul (op W.unop.left) a _).symm) }
  naturality W W' g := by
    ext m
    exact (sliceRootSection_naturality V κ hζ g.unop m.down).symm

/-- `sliceRootPresheafHom` sends `m` to the section `ζ^m`. -/
theorem sliceRootPresheafHom_app_apply (W : (Over V)ᵒᵖ) (m : ULift.{max (u + 1) v} (ZMod N)) :
    (sliceRootPresheafHom.{u, v} V κ hζ).app W m = sliceRootSection.{u, v} V κ hζ W.unop m.down :=
  rfl

/-- On a nonempty object of the slice, `m ↦ ζ^m` is injective. -/
theorem sliceRootSection_injective (W : Over V) [Nonempty W.left.left] :
    Function.Injective (sliceRootSection.{u, v} V κ hζ W) := by
  intro a b h
  have h1 := congrArg ((rootsOfUnityι.{u, v} X N).hom.app (op W.left)) h
  rw [rootsOfUnityι_sliceRootSection, rootsOfUnityι_sliceRootSection] at h1
  have h2 := congrArg Units.val (ofUnit_injective.{u, v} h1)
  have : Nontrivial Γ(W.left.left, ⊤) := by
    obtain ⟨p⟩ := ‹Nonempty W.left.left›
    have : Nonempty (⊤ : W.left.left.Opens) := ⟨⟨p, trivial⟩⟩
    infer_instance
  simp only [sliceRootOn, Units.val_pow_eq_pow_val, Units.coe_map, Units.val_mk0,
    ← map_pow] at h2
  have h3 := (sliceStructMap V κ W).injective h2
  exact ZMod.val_injective N (hζ.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) h3)

/-- Every sieve on an object of the slice with empty underlying scheme is covering. -/
theorem mem_over_smallEtaleTopology_of_isEmpty (W : Over V) (hW : IsEmpty W.left.left)
    (S : Sieve W) : S ∈ (X.smallEtaleTopology.over V) W :=
  (GrothendieckTopology.mem_over_iff _ _).2 (mem_smallEtaleTopology_of_isEmpty W.left hW _)

/-- `m ↦ ζ^m` is locally injective. -/
instance isLocallyInjective_sliceRootPresheafHom :
    Presheaf.IsLocallyInjective (X.smallEtaleTopology.over V)
      (sliceRootPresheafHom.{u, v} V κ hζ) where
  equalizerSieve_mem {W} a b h := by
    rcases isEmpty_or_nonempty W.unop.left.left with hW | hW
    · exact mem_over_smallEtaleTopology_of_isEmpty V W.unop hW _
    · rw [ULift.ext (sliceRootSection_injective V κ hζ W.unop h),
        Presheaf.equalizerSieve_self_eq_top]
      exact GrothendieckTopology.top_mem _ _

/-- **`m ↦ ζ^m` is locally surjective**: a section of `μ_N` over an object of the slice is `ζ^i`
on each of the basic open sets of the Lagrange idempotents of its root of unity. -/
theorem imageSieve_sliceRootPresheafHom_mem (W : Over V)
    (s : ToType (((X.smallEtaleTopology.overPullback (ModuleCat.{max (u + 1) v} (ZMod N)) V).obj
      (rootsOfUnityModule.{u, v} X N)).obj.obj (op W))) :
    Presheaf.imageSieve (sliceRootPresheafHom.{u, v} V κ hζ) s ∈
      (X.smallEtaleTopology.over V) W := by
  classical
  have hn : N ≠ 0 := NeZero.ne N
  let x : (Γ(W.left.left, ⊤))ˣ := (rootsOfUnitySection.{u, v} X N (op W.left) s).1
  let : Algebra k Γ(W.left.left, ⊤) := (sliceStructMap V κ W).toAlgebra
  have hxn : (x : Γ(W.left.left, ⊤)) ^ N = 1 := by
    rw [← Units.val_pow_eq_pow_val, (rootsOfUnitySection.{u, v} X N (op W.left) s).2,
      Units.val_one]
  let S := Polynomial.nthRootsFinset N (1 : k)
  let e : S → Γ(W.left.left, ⊤) := fun ρ => rootIdempotent (x : Γ(W.left.left, ⊤)) N ρ.1
  let Z : S → X.Etale := fun ρ =>
    Scheme.Etale.mk ((W.left.left.basicOpen (e ρ)).ι ≫ W.left.hom)
  let g : (ρ : S) → Z ρ ⟶ W.left := fun ρ =>
    MorphismProperty.Over.homMk (W.left.left.basicOpen (e ρ)).ι rfl
  have hcov : Sieve.ofArrows Z g ∈ X.smallEtaleTopology W.left := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    have hspan : Ideal.span (Set.range e) = ⊤ := by
      rw [Ideal.eq_top_iff_one, ← sum_rootIdempotent hζ hn (x : Γ(W.left.left, ⊤)),
        ← Finset.sum_coe_sort]
      exact Ideal.sum_mem _ fun ρ _ => Ideal.subset_span ⟨ρ, rfl⟩
    have h := AlgebraicGeometry.iSup_basicOpen_of_span_eq_top (X := W.left.left) ⊤ _ hspan
    refine Set.eq_univ_of_forall fun p => ?_
    have hp : p ∈ (⨆ i ∈ Set.range e, W.left.left.basicOpen i) := by rw [h]; trivial
    simp only [TopologicalSpace.Opens.mem_iSup, Set.mem_range, exists_prop] at hp
    obtain ⟨_, ⟨ρ, rfl⟩, hρ⟩ := hp
    exact Set.mem_iUnion.2 ⟨ρ, by
      change p ∈ Set.range (W.left.left.basicOpen (e ρ)).ι
      rw [Scheme.Opens.range_ι]
      exact hρ⟩
  refine (X.smallEtaleTopology.over V).superset_covering ?_
    (GrothendieckTopology.overEquiv_symm_mem_over _ W _ hcov)
  intro T f hf
  rw [Sieve.overEquiv_symm_iff] at hf
  obtain ⟨ρ, h, hfac⟩ := (Sieve.mem_ofArrows_iff Z g f.left).mp hf
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one
    ((Polynomial.mem_nthRootsFinset (Nat.pos_of_ne_zero hn) (1 : k)).1 ρ.2)
  refine ⟨ULift.up (i : ZMod N), ?_⟩
  change sliceRootSection.{u, v} V κ hζ T (i : ZMod N) =
    (rootsOfUnitySheaf.{u, v} X N).obj.map f.left.op s
  apply rootsOfUnityι_app_injective.{u, v} N T.left
  rw [rootsOfUnityι_sliceRootSection]
  erw [NatTrans.naturality_apply]
  have hx : (rootsOfUnityι.{u, v} X N).hom.app (op W.left) s = ofUnit.{u, v} x := rfl
  rw [hx, map_ofUnit]
  congr 1
  apply Units.ext
  have hunit := isUnit_ι_appTop_basicOpen W.left.left (e ρ)
  have hzero := sub_mul_rootIdempotent hζ hn (x : Γ(W.left.left, ⊤)) hxn ρ.2
  have himg := congrArg (W.left.left.basicOpen (e ρ)).ι.appTop.hom hzero
  rw [map_mul, map_zero, map_sub] at himg
  have hxρ := sub_eq_zero.1 (hunit.mul_left_eq_zero.1 himg)
  rw [Units.val_pow_eq_pow_val, Units.coe_map]
  change sliceStructMap V κ T ζ ^ (i : ZMod N).val =
    f.left.left.appTop.hom (x : Γ(W.left.left, ⊤))
  have happ : f.left.left.appTop.hom =
      h.left.appTop.hom.comp (W.left.left.basicOpen (e ρ)).ι.appTop.hom := by
    rw [show f.left.left = h.left ≫ (W.left.left.basicOpen (e ρ)).ι from
      congrArg (fun q : T.left ⟶ W.left => q.left) hfac]
    exact congrArg CommRingCat.Hom.hom (Scheme.Hom.comp_appTop _ _)
  rw [ZMod.val_natCast, ← map_pow, ← pow_eq_pow_mod_of_pow_eq_one hζ.pow_eq_one, hi,
    ← sliceStructMap_comp V κ f, RingHom.comp_apply, happ]
  exact congrArg h.left.appTop.hom hxρ.symm

section Sheaf

attribute [local instance] Stacks.ConstantSheaf.hasSheafify_moduleCat_of_univLE

variable [HasWeakSheafify (X.smallEtaleTopology.over V) (ModuleCat.{max (u + 1) v} (ZMod N))]

/-- **`ℤ/N ⟶ μ_N|_V`, `m ↦ ζ^m`**, as a morphism out of the constant sheaf on the slice. -/
def sliceRootSheafHom :
    (presheafToSheaf (X.smallEtaleTopology.over V) (ModuleCat.{max (u + 1) v} (ZMod N))).obj
        (sliceConstantPresheaf V N) ⟶
      (X.smallEtaleTopology.overPullback (ModuleCat.{max (u + 1) v} (ZMod N)) V).obj
        (rootsOfUnityModule.{u, v} X N) :=
  ((sheafificationAdjunction (X.smallEtaleTopology.over V)
    (ModuleCat.{max (u + 1) v} (ZMod N))).homEquiv _ _).symm (sliceRootPresheafHom.{u, v} V κ hζ)

/-- `sliceRootSheafHom` restricts to `sliceRootPresheafHom` along the sheafification map. -/
@[reassoc]
theorem toSheafify_sliceRootSheafHom :
    toSheafify (X.smallEtaleTopology.over V) _ ≫ (sliceRootSheafHom.{u, v} V κ hζ).hom =
      sliceRootPresheafHom.{u, v} V κ hζ :=
  toSheafify_sheafifyLift _ _ _

/-- `m ↦ ζ^m` is locally surjective. -/
instance isLocallySurjective_sliceRootPresheafHom :
    Presheaf.IsLocallySurjective (X.smallEtaleTopology.over V)
      (sliceRootPresheafHom.{u, v} V κ hζ) where
  imageSieve_mem {W} s := imageSieve_sliceRootPresheafHom_mem V κ hζ W s

/-- **`m ↦ ζ^m` is an isomorphism `ℤ/N ≅ μ_N` on the slice at `V`.** -/
theorem isIso_sliceRootSheafHom : IsIso (sliceRootSheafHom.{u, v} V κ hζ) := by
  have : Presheaf.IsLocallySurjective (X.smallEtaleTopology.over V)
      (toSheafify (X.smallEtaleTopology.over V) _ ≫ (sliceRootSheafHom.{u, v} V κ hζ).hom) := by
    rw [toSheafify_sliceRootSheafHom]
    infer_instance
  have : Sheaf.IsLocallySurjective (sliceRootSheafHom.{u, v} V κ hζ) :=
    Presheaf.isLocallySurjective_of_isLocallySurjective (X.smallEtaleTopology.over V)
      (toSheafify (X.smallEtaleTopology.over V) _) (sliceRootSheafHom.{u, v} V κ hζ).hom
  have : Sheaf.IsLocallyInjective (sliceRootSheafHom.{u, v} V κ hζ) :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac
      (X.smallEtaleTopology.over V) (sliceRootPresheafHom.{u, v} V κ hζ)
      (toSheafify_sliceRootSheafHom V κ hζ)
  exact (Sheaf.isLocallyBijective_iff_isIso _).1 ⟨inferInstance, inferInstance⟩

/-- **`ℤ/N ≅ μ_N` on the slice at `V`**, by `m ↦ ζ^m`. -/
def sliceRootSheafIso :
    (presheafToSheaf (X.smallEtaleTopology.over V) (ModuleCat.{max (u + 1) v} (ZMod N))).obj
        (sliceConstantPresheaf V N) ≅
      (X.smallEtaleTopology.overPullback (ModuleCat.{max (u + 1) v} (ZMod N)) V).obj
        (rootsOfUnityModule.{u, v} X N) :=
  haveI := isIso_sliceRootSheafHom V κ hζ
  asIso (sliceRootSheafHom.{u, v} V κ hζ)

include κ hζ in
/-- **`μ_N` restricted to an étale `X`-scheme carrying a primitive `N`-th root of unity is
constant.** -/
theorem isConstant_overPullback_rootsOfUnityModule :
    Sheaf.IsConstant (X.smallEtaleTopology.over V)
      ((X.smallEtaleTopology.overPullback (ModuleCat.{max (u + 1) v} (ZMod N)) V).obj
        (rootsOfUnityModule.{u, v} X N)) :=
  ⟨ModuleCat.of (ZMod N) (ULift.{max (u + 1) v} (ZMod N)), ⟨sliceRootSheafIso V κ hζ⟩⟩

end Sheaf

end Stacks.Kummer

end
