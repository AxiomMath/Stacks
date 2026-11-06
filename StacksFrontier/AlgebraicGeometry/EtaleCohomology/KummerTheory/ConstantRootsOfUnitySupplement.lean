module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.MultiplicativeSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.ConstantSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.ConstantSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.ConstantRootsOfUnity
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `μ_n ≅ 𝐙/n𝐙` on the small étale site of a scheme over an algebraically closed field

Let `B` be a big étale site containing a scheme `X`, let `k` be an algebraically closed field,
let `X` be a `k`-scheme and let `n ≥ 1` be invertible in `k`. Then the sheaf `μ_n` of `n`-th
roots of unity on the small étale site of `X` is isomorphic, as a sheaf of abelian groups, to
the constant sheaf with value `𝐙/n𝐙`.

The isomorphism is not canonical: it is induced by a group isomorphism `𝐙/n𝐙 ≅ μ_n(k)`, and
there are `φ(n)` of those. It is the sheafification of the comparison
`AlgebraicGeometry.ConstantRootsOfUnity.constToRoots` from the constant presheaf with value
`𝐙/n𝐙` to `μ_n`, which is locally bijective.

## Main definitions

* `AlgebraicGeometry.ConstantRootsOfUnity.constToUnits` and
  `AlgebraicGeometry.ConstantRootsOfUnity.constToRoots`: the comparison from the constant
  presheaf with value `𝐙/n𝐙` to `𝐆_m` and to `μ_n`.
* `AlgebraicGeometry.constantZModSheafIsoRootsOfUnitySheaf`: `𝐙/n𝐙 ≅ μ_n` as sheaves of abelian
  groups on the small étale site.

## Main results

* `AlgebraicGeometry.ConstantRootsOfUnity.constToRoots_isLocallyInjective` and
  `AlgebraicGeometry.ConstantRootsOfUnity.constToRoots_isLocallySurjective`: the comparison is
  locally bijective.
* `AlgebraicGeometry.ConstantRootsOfUnity.exists_cover_const_of_pow_eq_one`: a root of unity in
  the sections over an étale `X`-scheme is, on a covering family, one of the `n` constants.

## References

* [Stacks Project, Tag 03RQ](https://stacks.math.columbia.edu/tag/03RQ)
* [Stacks Project, Tag 03P5](https://stacks.math.columbia.edu/tag/03P5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace ConstantRootsOfUnity

/-! ### The comparison from the constant presheaf -/

/-- The structure ring homomorphism of the base field into the global functions. -/
def baseHom (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) :
    k →+* Scheme.Γ.obj (op X) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom

/-- The `n`-th roots of unity of the base field, as units of the global functions. -/
def cyclicToGlobalUnits (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (n : ℕ) (hn : 0 < n) (hnk : IsUnit (n : k)) :
    AddCommGrpCat.of (ULift.{u} (ZMod n)) ⟶
      AddCommGrpCat.of (Additive ((Scheme.Γ.obj (op X))ˣ)) :=
  AddCommGrpCat.ofHom
    (((MonoidHom.toAdditive
        ((Units.map (baseHom k f).toMonoidHom).comp (rootsOfUnity n k).subtype)).comp
      (zmodAddEquivRootsOfUnity k n hn hnk).toAddMonoidHom).comp
      (AddEquiv.ulift.{0, u} (α := ZMod n)).toAddMonoidHom)

variable (B : BigEtaleSite.{u}) (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (hX : B.Contains X) (n : ℕ) (hn : 0 < n) (hnk : IsUnit (n : k))

/-- The structure homomorphism of the base field into the sections over an étale object. -/
def structHom (T : SmallEtale B X hX) :
    k →+* Scheme.Γ.obj (op ((SmallEtale.toScheme B X hX).obj T)) :=
  ((Scheme.Γ.map ((SmallEtale.toScheme B X hX).map
    ((SmallEtale.finalIsTerminal B X hX).from T)).op).hom).comp (baseHom k f)

omit [IsAlgClosed k] in
/-- The structure homomorphisms are compatible with restriction along a morphism of the small
étale site. -/
theorem structHom_naturality {T T' : SmallEtale B X hX} (g : T' ⟶ T) (x : k) :
    (Scheme.Γ.map ((SmallEtale.toScheme B X hX).map g).op).hom
        (structHom B k f hX T x) = structHom B k f hX T' x := by
  have hcomp : g ≫ (SmallEtale.finalIsTerminal B X hX).from T =
      (SmallEtale.finalIsTerminal B X hX).from T' :=
    (SmallEtale.finalIsTerminal B X hX).hom_ext _ _
  change (Scheme.Γ.map ((SmallEtale.toScheme B X hX).map g).op).hom
      ((Scheme.Γ.map ((SmallEtale.toScheme B X hX).map
        ((SmallEtale.finalIsTerminal B X hX).from T)).op).hom (baseHom k f x)) = _
  change ((Scheme.Γ.map ((SmallEtale.toScheme B X hX).map
        ((SmallEtale.finalIsTerminal B X hX).from T)).op) ≫
      (Scheme.Γ.map ((SmallEtale.toScheme B X hX).map g).op)).hom (baseHom k f x) = _
  rw [← Scheme.Γ.map_comp, ← op_comp, ← Functor.map_comp, hcomp]
  rfl

/-- The comparison from the constant presheaf with value `𝐙/n𝐙` to `𝐆_m`, sending a residue
class to the corresponding constant root of unity. -/
def constToUnits :
    (Functor.const (SmallEtale B X hX)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} (ZMod n))) ⟶
      unitsPresheaf (SmallEtale.toScheme B X hX) where
  app T := (show AddCommGrpCat.of (ULift.{u} (ZMod n)) ⟶
        (unitsPresheaf (SmallEtale.toScheme B X hX)).obj (op (SmallEtale.final B X hX)) from
      cyclicToGlobalUnits k f n hn hnk) ≫
    (unitsPresheaf (SmallEtale.toScheme B X hX)).map
      ((SmallEtale.finalIsTerminal B X hX).from T.unop).op
  naturality T T' g := by
    have hcomp : (SmallEtale.finalIsTerminal B X hX).from T'.unop =
        g.unop ≫ (SmallEtale.finalIsTerminal B X hX).from T.unop :=
      (SmallEtale.finalIsTerminal B X hX).hom_ext _ _
    dsimp only [Functor.const_obj_map]
    rw [hcomp, op_comp, Functor.map_comp]
    exact (Category.assoc _ _ _).symm

/-- The comparison `constToUnits` sends the residue class `j` over `T` to the image of the root
of unity `zeta k n hn hnk j` under `structHom`. -/
theorem constToUnits_app_val (T : SmallEtale B X hX) (j : ZMod n) :
    ((Additive.toMul ((constToUnits B k f hX n hn hnk).app (op T) (ULift.up j)) :
        (Scheme.Γ.obj (op ((SmallEtale.toScheme B X hX).obj T)))ˣ) :
        Scheme.Γ.obj (op ((SmallEtale.toScheme B X hX).obj T))) =
      structHom B k f hX T ((zeta k n hn hnk j : kˣ) : k) := rfl

end ConstantRootsOfUnity

namespace ConstantRootsOfUnity

/-! ### Elementary lemmas -/

/-- In `Additive A`, the `m`-fold multiple corresponds to the `m`-th power in `A`. -/
theorem additive_nsmul_toMul (A : Type u) [CommGroup A] (m : ℕ) (x : Additive A) :
    Additive.toMul (m • x) = (Additive.toMul x) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [succ_nsmul, Additive.toMul]
      simp [ih, pow_succ]

/-! ### The comparison to `μ_n` and its local bijectivity -/

section

variable (B : BigEtaleSite.{u}) (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (hX : B.Contains X) (n : ℕ) (hn : 0 < n) (hnk : IsUnit (n : k))
  [HasSheafify (SmallEtale.topology B X hX) AddCommGrpCat.{u}]

omit [HasSheafify (SmallEtale.topology B X hX) AddCommGrpCat] in
/-- The comparison `constToUnits` followed by the `n`-th power map of `𝐆_m` is zero. -/
theorem constToUnits_comp_power :
    constToUnits B k f hX n hn hnk ≫
      (sheafToPresheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u}).map
        (powerSheaf (SmallEtale.topology B X hX) (SmallEtale.toScheme B X hX)
          (unitsPresheaf_isSheaf_smallEtale B X hX) n) = 0 := by
  have key : ∀ (T : (SmallEtale B X hX)ᵒᵖ) (x : ULift.{u} (ZMod n)),
      ((constToUnits B k f hX n hn hnk ≫
        (sheafToPresheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u}).map
          (powerSheaf (SmallEtale.topology B X hX) (SmallEtale.toScheme B X hX)
            (unitsPresheaf_isSheaf_smallEtale B X hX) n)).app T).hom x = 0 := by
    intro T x
    have hx : (n • x : ULift.{u} (ZMod n)) = 0 := by
      apply ULift.ext
      change n • x.down = (0 : ZMod n)
      rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    have h1 : ((constToUnits B k f hX n hn hnk ≫
        (sheafToPresheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u}).map
          (powerSheaf (SmallEtale.topology B X hX) (SmallEtale.toScheme B X hX)
            (unitsPresheaf_isSheaf_smallEtale B X hX) n)).app T).hom x =
        n • (((constToUnits B k f hX n hn hnk).app T).hom x) := rfl
    rw [h1, ← map_nsmul, hx]
    exact map_zero _
  ext T x
  exact key T x

/-- The comparison from the constant presheaf with value `𝐙/n𝐙` to `μ_n`, sending a residue
class to the corresponding constant root of unity. -/
def constToRoots :
    (Functor.const (SmallEtale B X hX)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} (ZMod n))) ⟶
      (rootsOfUnitySheaf (SmallEtale.topology B X hX) (SmallEtale.toScheme B X hX)
        (unitsPresheaf_isSheaf_smallEtale B X hX) n).obj :=
  kernel.lift
      ((sheafToPresheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u}).map
        (powerSheaf (SmallEtale.topology B X hX) (SmallEtale.toScheme B X hX)
          (unitsPresheaf_isSheaf_smallEtale B X hX) n))
      (constToUnits B k f hX n hn hnk) (constToUnits_comp_power B k f hX n hn hnk) ≫
    (PreservesKernel.iso
      (sheafToPresheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u})
      (powerSheaf (SmallEtale.topology B X hX) (SmallEtale.toScheme B X hX)
        (unitsPresheaf_isSheaf_smallEtale B X hX) n)).inv

/-- The comparison `constToRoots`, followed by the inclusion of `μ_n` into `𝐆_m`, is
`constToUnits`. -/
theorem constToRoots_comp_ι :
    constToRoots B k f hX n hn hnk ≫
        (kernel.ι (powerSheaf (SmallEtale.topology B X hX) (SmallEtale.toScheme B X hX)
          (unitsPresheaf_isSheaf_smallEtale B X hX) n)).hom =
      constToUnits B k f hX n hn hnk := by
  let E := sheafToPresheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u}
  let p := powerSheaf (SmallEtale.topology B X hX) (SmallEtale.toScheme B X hX)
    (unitsPresheaf_isSheaf_smallEtale B X hX) n
  have h1 : (PreservesKernel.iso E p).inv ≫ E.map (kernel.ι p) = kernel.ι (E.map p) := by
    rw [Iso.inv_comp_eq, PreservesKernel.iso_hom]
    exact (kernelComparison_comp_ι p E).symm
  change (kernel.lift (E.map p) (constToUnits B k f hX n hn hnk)
      (constToUnits_comp_power B k f hX n hn hnk) ≫
      (PreservesKernel.iso E p).inv) ≫ E.map (kernel.ι p) = _
  rw [Category.assoc, h1]
  exact kernel.lift_ι _ _ _

/-- The inclusion of `μ_n` into `𝐆_m` sends `constToRoots` to `constToUnits`, sectionwise. -/
private theorem kernel_ι_app_constToRoots (T : (SmallEtale B X hX)ᵒᵖ)
    (x : ULift.{u} (ZMod n)) :
    (kernel.ι (powerSheaf (SmallEtale.topology B X hX) (SmallEtale.toScheme B X hX)
        (unitsPresheaf_isSheaf_smallEtale B X hX) n)).hom.app T
        ((constToRoots B k f hX n hn hnk).app T x) =
      (constToUnits B k f hX n hn hnk).app T x :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (constToRoots_comp_ι B k f hX n hn hnk) T) x

/-- A section of `μ_n` is determined by the invertible global function underlying it. -/
theorem rootsSheaf_ι_app_injective (T : SmallEtale B X hX) :
    Function.Injective ((kernel.ι (powerSheaf (SmallEtale.topology B X hX)
      (SmallEtale.toScheme B X hX) (unitsPresheaf_isSheaf_smallEtale B X hX) n)).hom.app
        (op T)) := by
  let J := SmallEtale.topology B X hX
  let p := powerSheaf J (SmallEtale.toScheme B X hX)
    (unitsPresheaf_isSheaf_smallEtale B X hX) n
  let E : Sheaf J AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
    sheafToPresheaf J AddCommGrpCat ⋙ (evaluation _ _).obj (op T)
  let : PreservesLimit (parallelPair p 0) E := inferInstance
  have hc : kernelComparison p E ≫ kernel.ι (E.map p) = E.map (kernel.ι p) :=
    kernelComparison_comp_ι p E
  have hiso : IsIso (kernelComparison p E) := by
    rw [← PreservesKernel.iso_hom]
    infer_instance
  have h1 : Function.Injective (kernelComparison p E) :=
    (AddCommGrpCat.mono_iff_injective _).1 inferInstance
  have h2 : Function.Injective (kernel.ι (E.map p)) :=
    (AddCommGrpCat.mono_iff_injective _).1 inferInstance
  intro a b hab
  apply h1
  apply h2
  rwa [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, hc]

omit [HasSheafify (SmallEtale.topology B X hX) AddCommGrpCat] in
/-- The comparison from the constant presheaf with value `𝐙/n𝐙` to `𝐆_m` is locally injective. -/
theorem constToUnits_isLocallyInjective :
    Presheaf.IsLocallyInjective (SmallEtale.topology B X hX)
      (constToUnits B k f hX n hn hnk) := by
  refine ⟨fun {T} a b hab => ?_⟩
  by_cases hab' : a = b
  · subst hab'
    simp
  · have hne : ((zeta k n hn hnk a.down : kˣ) : k) -
        ((zeta k n hn hnk b.down : kˣ) : k) ≠ 0 := by
      intro h
      exact hab' (ULift.ext (zeta_injective k n hn hnk (sub_eq_zero.1 h)))
    have hval : structHom B k f hX T.unop ((zeta k n hn hnk a.down : kˣ) : k) =
        structHom B k f hX T.unop ((zeta k n hn hnk b.down : kˣ) : k) :=
      (constToUnits_app_val B k f hX n hn hnk T.unop a.down).symm.trans
        ((congrArg (fun z => (Additive.toMul z).val) hab).trans
          (constToUnits_app_val B k f hX n hn hnk T.unop b.down))
    have hzero : (1 : Scheme.Γ.obj (op ((SmallEtale.toScheme B X hX).obj T.unop))) = 0 := by
      refine one_eq_zero_of_map_eq_zero (structHom B k f hX T.unop) hne ?_
      rw [map_sub, hval, sub_self]
    have hempty : IsEmpty ((SmallEtale.toScheme B X hX).obj T.unop) :=
      isEmpty_of_one_eq_zero hzero
    have heq : Presheaf.equalizerSieve
        (F := (Functor.const (SmallEtale B X hX)ᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u} (ZMod n)))) (X := T) a b = ⊥ := by
      ext Y g
      simp only [Presheaf.equalizerSieve_apply, Sieve.bot_apply]
      exact ⟨fun hf => (hab' (by simpa using hf)).elim, False.elim⟩
    rw [heq]
    exact openCoverData_bottom (SmallEtale.toScheme B X hX) (SmallEtale.topology B X hX)
      (smallEtale_openCoverData B X hX) hempty

/-- The comparison from the constant presheaf with value `𝐙/n𝐙` to `μ_n` is locally injective. -/
theorem constToRoots_isLocallyInjective :
    Presheaf.IsLocallyInjective (SmallEtale.topology B X hX)
      (constToRoots B k f hX n hn hnk) := by
  refine ⟨fun {T} x y hxy => ?_⟩
  refine (constToUnits_isLocallyInjective B k f hX n hn hnk).equalizerSieve_mem x y ?_
  exact (kernel_ι_app_constToRoots B k f hX n hn hnk T x).symm.trans
    ((congrArg _ hxy).trans (kernel_ι_app_constToRoots B k f hX n hn hnk T y))

omit [HasSheafify (SmallEtale.topology B X hX) AddCommGrpCat] in
/-- A root of unity in the sections over an étale `X`-scheme is, on a covering family of the
small étale site, one of the `n` constants. -/
theorem exists_cover_const_of_pow_eq_one {ζ : k} (hζ : IsPrimitiveRoot ζ n)
    (T : SmallEtale B X hX)
    (w : Scheme.Γ.obj (op ((SmallEtale.toScheme B X hX).obj T))) (hw : w ^ n = 1) :
    ∃ (I : Type (u + 1)) (W : I → SmallEtale B X hX) (a : ∀ i, W i ⟶ T) (jj : I → ZMod n),
      Sieve.ofArrows W a ∈ SmallEtale.topology B X hX T ∧
        ∀ i, (Scheme.Γ.map ((SmallEtale.toScheme B X hX).map (a i)).op).hom w =
          structHom B k f hX (W i) ((zeta k n hn hnk (jj i) : kˣ) : k) := by
  classical
  have hgeom := fun y => exists_open_pullback_eq_const hn hζ
    ((SmallEtale.toScheme B X hX).obj T) (structHom B k f hX T) w hw y
  choose V ξ hyV hξ hpull using hgeom
  have hVcover : TopologicalSpace.IsOpenCover V := by
    rw [TopologicalSpace.IsOpenCover]
    refine le_antisymm le_top ?_
    intro x _
    rw [TopologicalSpace.Opens.mem_iSup]
    exact ⟨x, hyV x⟩
  obtain ⟨I, W, a, r, hcover, hmaps⟩ := smallEtale_openCoverData B X hX V hVcover
  have hjex : ∀ i : I, ∃ j : ZMod n, ((zeta k n hn hnk j : kˣ) : k) = ξ (r i) :=
    fun i => exists_zeta_eq k n hn hnk (hξ (r i))
  choose jj hjj using hjex
  refine ⟨I, W, a, jj, hcover, fun i => ?_⟩
  rw [hjj i, ← structHom_naturality B k f hX (a i)]
  exact hpull (r i) _ ((SmallEtale.toScheme B X hX).map (a i)) (hmaps i)

/-- The comparison from the constant presheaf with value `𝐙/n𝐙` to `μ_n` is locally
surjective. -/
theorem constToRoots_isLocallySurjective :
    Presheaf.IsLocallySurjective (SmallEtale.topology B X hX)
      (constToRoots B k f hX n hn hnk) := by
  classical
  obtain ⟨ζ, hζ⟩ : ∃ ζ : k, IsPrimitiveRoot ζ n := by
    let : NeZero n := ⟨Nat.ne_of_gt hn⟩
    let : NeZero (n : k) := ⟨hnk.ne_zero⟩
    let : HasEnoughRootsOfUnity k n := inferInstance
    exact HasEnoughRootsOfUnity.exists_primitiveRoot k n
  refine ⟨fun {T} s => ?_⟩
  have hnsmul : n • (((kernel.ι (powerSheaf (SmallEtale.topology B X hX)
        (SmallEtale.toScheme B X hX) (unitsPresheaf_isSheaf_smallEtale B X hX)
          n)).hom.app (op T)) s) = 0 :=
    congrArg (fun φ : kernel (powerSheaf (SmallEtale.topology B X hX)
        (SmallEtale.toScheme B X hX) (unitsPresheaf_isSheaf_smallEtale B X hX) n) ⟶
          unitsSheaf (SmallEtale.topology B X hX) (SmallEtale.toScheme B X hX)
            (unitsPresheaf_isSheaf_smallEtale B X hX) =>
      (φ.hom.app (op T)) s)
      (kernel.condition (powerSheaf (SmallEtale.topology B X hX)
        (SmallEtale.toScheme B X hX) (unitsPresheaf_isSheaf_smallEtale B X hX) n))
  have hwn : ((Additive.toMul (((kernel.ι (powerSheaf (SmallEtale.topology B X hX)
        (SmallEtale.toScheme B X hX) (unitsPresheaf_isSheaf_smallEtale B X hX)
          n)).hom.app (op T)) s)).val :
      Scheme.Γ.obj (op ((SmallEtale.toScheme B X hX).obj T))) ^ n = 1 := by
    have h2 : (n • (((kernel.ι (powerSheaf (SmallEtale.topology B X hX)
        (SmallEtale.toScheme B X hX) (unitsPresheaf_isSheaf_smallEtale B X hX)
          n)).hom.app (op T)) s) :
        Additive ((Scheme.Γ.obj (op ((SmallEtale.toScheme B X hX).obj T)))ˣ)) = 0 := hnsmul
    have h5 : (Additive.toMul (((kernel.ι (powerSheaf (SmallEtale.topology B X hX)
        (SmallEtale.toScheme B X hX) (unitsPresheaf_isSheaf_smallEtale B X hX)
          n)).hom.app (op T)) s) :
        (Scheme.Γ.obj (op ((SmallEtale.toScheme B X hX).obj T)))ˣ) ^ n = 1 :=
      (additive_nsmul_toMul _ n _).symm.trans (congrArg Additive.toMul h2)
    have h6 := congrArg Units.val h5
    rw [Units.val_pow_eq_pow_val, Units.val_one] at h6
    exact h6
  obtain ⟨I, W, a, jj, hcover, heq⟩ :=
    exists_cover_const_of_pow_eq_one B k f hX n hn hnk hζ T _ hwn
  refine (SmallEtale.topology B X hX).superset_covering ?_ hcover
  intro Z g hg
  obtain ⟨i, g', rfl⟩ := (Sieve.mem_ofArrows_iff W a g).mp hg
  apply (Presheaf.imageSieve (constToRoots B k f hX n hn hnk) s).downward_closed
  refine ⟨ULift.up (jj i), ?_⟩
  apply rootsSheaf_ι_app_injective B hX n (W i)
  have hstep1 := kernel_ι_app_constToRoots B k f hX n hn hnk (op (W i)) (ULift.up (jj i))
  have hL := constToUnits_app_val B k f hX n hn hnk (W i) (jj i)
  have hR : (Additive.toMul ((unitsPresheaf (SmallEtale.toScheme B X hX)).map (a i).op
        (((kernel.ι (powerSheaf (SmallEtale.topology B X hX)
          (SmallEtale.toScheme B X hX) (unitsPresheaf_isSheaf_smallEtale B X hX)
            n)).hom.app (op T)) s))).val =
      (Scheme.Γ.map ((SmallEtale.toScheme B X hX).map (a i)).op).hom
        (Additive.toMul (((kernel.ι (powerSheaf (SmallEtale.topology B X hX)
          (SmallEtale.toScheme B X hX) (unitsPresheaf_isSheaf_smallEtale B X hX)
            n)).hom.app (op T)) s)).val := rfl
  have hstep2 : (constToUnits B k f hX n hn hnk).app (op (W i)) (ULift.up (jj i)) =
      (unitsPresheaf (SmallEtale.toScheme B X hX)).map (a i).op
        (((kernel.ι (powerSheaf (SmallEtale.topology B X hX)
          (SmallEtale.toScheme B X hX) (unitsPresheaf_isSheaf_smallEtale B X hX)
            n)).hom.app (op T)) s) :=
    Additive.toMul.injective (Units.ext (hL.trans ((heq i).symm.trans hR.symm)))
  have hstep3 : (((kernel.ι (powerSheaf (SmallEtale.topology B X hX)
        (SmallEtale.toScheme B X hX) (unitsPresheaf_isSheaf_smallEtale B X hX)
          n)).hom.app (op (W i)))
        ((rootsOfUnitySheaf (SmallEtale.topology B X hX) (SmallEtale.toScheme B X hX)
          (unitsPresheaf_isSheaf_smallEtale B X hX) n).obj.map (a i).op s)) =
      (unitsPresheaf (SmallEtale.toScheme B X hX)).map (a i).op
        (((kernel.ι (powerSheaf (SmallEtale.topology B X hX)
          (SmallEtale.toScheme B X hX) (unitsPresheaf_isSheaf_smallEtale B X hX)
            n)).hom.app (op T)) s) :=
    NatTrans.naturality_apply (kernel.ι (powerSheaf (SmallEtale.topology B X hX)
      (SmallEtale.toScheme B X hX) (unitsPresheaf_isSheaf_smallEtale B X hX) n)).hom (a i).op s
  exact (hstep1.trans hstep2).trans hstep3.symm

end

end ConstantRootsOfUnity

/-- **`𝐙/n𝐙 ≅ μ_n` as sheaves of abelian groups on the small étale site.** Let `k` be an
algebraically closed field, `X` a `k`-scheme inside a big étale site `B`, and `n ≥ 1`
invertible in `k`. The constant sheaf with value `𝐙/n𝐙` on the small étale site of `X` is
isomorphic to the sheaf `μ_n` of `n`-th roots of unity.

The isomorphism depends on the choice of isomorphism `𝐙/n𝐙 ≅ μ_n(k)` made by
`AlgebraicGeometry.zmodAddEquivRootsOfUnity`. -/
@[sga "4½ Arcata 2.2.4" "special case",
  sga "4½ Arcata 3.3.5" "more general",
  sga "5 VI 3.2" "partial"]
def constantZModSheafIsoRootsOfUnitySheaf (B : BigEtaleSite.{u}) (k : Type u) [Field k]
    [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (hX : B.Contains X) (n : ℕ)
    (hn : 0 < n) (hnk : IsUnit (n : k))
    [HasSheafify (SmallEtale.topology B X hX) AddCommGrpCat.{u}]
    [(SmallEtale.topology B X hX).WEqualsLocallyBijective AddCommGrpCat.{u}] :
    (constantSheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} (ZMod n))) ≅
      rootsOfUnitySheaf (SmallEtale.topology B X hX) (SmallEtale.toScheme B X hX)
        (unitsPresheaf_isSheaf_smallEtale B X hX) n := by
  haveI := ConstantRootsOfUnity.constToRoots_isLocallyInjective B k f hX n hn hnk
  haveI := ConstantRootsOfUnity.constToRoots_isLocallySurjective B k f hX n hn hnk
  have hα : IsIso ((presheafToSheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u}).map
      (ConstantRootsOfUnity.constToRoots B k f hX n hn hnk)) := by
    rw [← (SmallEtale.topology B X hX).W_iff]
    exact ((SmallEtale.topology B X hX).W_iff_isLocallyBijective _).mpr
      ⟨inferInstance, inferInstance⟩
  let R := rootsOfUnitySheaf (SmallEtale.topology B X hX) (SmallEtale.toScheme B X hX)
    (unitsPresheaf_isSheaf_smallEtale B X hX) n
  let e₁ : (constantSheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} (ZMod n))) ≅
      (presheafToSheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u}).obj
        ((Functor.const (SmallEtale B X hX)ᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u} (ZMod n)))) := Iso.refl _
  let e₂ := asIso ((presheafToSheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u}).map
    (ConstantRootsOfUnity.constToRoots B k f hX n hn hnk))
  let e₃ := asIso ((sheafificationAdjunction (SmallEtale.topology B X hX)
    AddCommGrpCat.{u}).counit.app R)
  exact (e₁.trans e₂).trans e₃

end AlgebraicGeometry

end
