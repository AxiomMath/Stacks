module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPullbackTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedTensorHomAdjunction

/-!
# The internal hom of sheaves of differential graded modules, constructed

Let `R` be a sheaf of commutative rings on a site `(C, J)`, let `A` be a sheaf of differential
graded `R`-algebras and let `K`, `L` be right differential graded `A`-modules. The local
sections of the degree-`n` part of the internal hom `SheafHom^dg_A(K, L)` over `U` are the
degree-`n` local homomorphisms `K|_U → L|_U`, the elements of `SheafOfModules.LocalHom`. This
file shows that these local sections form a sheaf of `R`-modules, and so constructs the internal
hom.

## Main definitions

* `SheafOfModules.LocalHom.diffAt`: the differential `d(f) = d_L ∘ f - (-1)^n f ∘ d_K` of a
  degree-`n` local homomorphism.
* `SheafOfModules.LocalHom.glue`: the local homomorphism glued from a compatible family over a
  covering sieve.
* `SheafOfModules.localHomPresheaf` and `SheafOfModules.localHomSheaf`: the presheaf, and the
  sheaf, of `R`-modules `U ↦ SheafHom^n_A(K, L)(U)`.
* `SheafOfModules.sheafHomComplex`: the internal hom `SheafHom^dg_A(K, L)` as a complex of
  sheaves of `R`-modules.

## Main results

* `SheafOfModules.localHomPresheaf_isSheaf`: the local homomorphisms form a sheaf.
* `SheafOfModules.LocalHom.diffAt_diffAt`: the differential squares to zero.
* `SheafOfModules.isInternalHom_sheafHomComplex`: the constructed complex *is* the internal hom
  in the sense of `SheafOfModules.IsInternalHom`.

## Implementation notes

The module structure is `(r f)(x) = r f(x)`; it needs the rings of sections of `R` to be
commutative, which is recorded by the instance argument `∀ U, IsMulCommutative (R.obj.obj U)`.
This holds for the structure sheaf of every ringed site.

## References

* [Stacks Project, Tag 0FRN](https://stacks.math.columbia.edu/tag/0FRN)
-/

@[expose] public section

open CategoryTheory Opposite

universe t a z s v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A : DifferentialGradedAlgebra.{t, a} R}

namespace LocalHom

variable {K : DifferentialGradedModule.{t, a, z} A} {L : DifferentialGradedModule.{t, a, s} A}
  {n : ℤ} {U : C}

/-! ### The additive group of local homomorphisms -/

/-- The zero local homomorphism. -/
instance : Zero (LocalHom K L n U) := ⟨LocalHom.zero K L n U⟩

/-- The pointwise sum of local homomorphisms. -/
instance : Add (LocalHom K L n U) where
  add f g :=
    { app := fun i j hij V => AddMonoidHom.mk' (fun x => f.app i j hij V x + g.app i j hij V x)
        (fun x y => by simp only [map_add]; abel)
      map_smul := fun i j hij V r x => by
        simp only [AddMonoidHom.mk'_apply, f.map_smul, g.map_smul, smul_add]
      naturality := fun i j hij V W q x => by
        simp only [AddMonoidHom.mk'_apply, map_add, f.naturality, g.naturality]
        rfl
      isLinear := fun i j hij p V x b => by
        simp only [AddMonoidHom.mk'_apply]
        rw [f.isLinear i j hij p V x b, g.isLinear i j hij p V x b, map_add,
          AddMonoidHom.add_apply] }

/-- The pointwise negation of a local homomorphism. -/
instance : Neg (LocalHom K L n U) where
  neg f :=
    { app := fun i j hij V => AddMonoidHom.mk' (fun x => -f.app i j hij V x)
        (fun x y => by simp only [map_add]; abel)
      map_smul := fun i j hij V r x => by
        simp only [AddMonoidHom.mk'_apply, f.map_smul, smul_neg]
      naturality := fun i j hij V W q x => by
        simp only [AddMonoidHom.mk'_apply, map_neg, f.naturality]
        rfl
      isLinear := fun i j hij p V x b => by
        simp only [AddMonoidHom.mk'_apply]
        rw [f.isLinear i j hij p V x b, map_neg, AddMonoidHom.neg_apply] }

/-- The pointwise difference of local homomorphisms. -/
instance : Sub (LocalHom K L n U) where
  sub f g :=
    { app := fun i j hij V => AddMonoidHom.mk' (fun x => f.app i j hij V x - g.app i j hij V x)
        (fun x y => by simp only [map_add]; abel)
      map_smul := fun i j hij V r x => by
        simp only [AddMonoidHom.mk'_apply, f.map_smul, g.map_smul, smul_sub]
      naturality := fun i j hij V W q x => by
        simp only [AddMonoidHom.mk'_apply, map_sub, f.naturality, g.naturality]
        rfl
      isLinear := fun i j hij p V x b => by
        simp only [AddMonoidHom.mk'_apply]
        rw [f.isLinear i j hij p V x b, g.isLinear i j hij p V x b, map_sub,
          AddMonoidHom.sub_apply] }

/-- The pointwise multiple of a local homomorphism by a natural number. -/
instance : SMul ℕ (LocalHom K L n U) where
  smul k f :=
    { app := fun i j hij V => AddMonoidHom.mk' (fun x => k • f.app i j hij V x)
        (fun x y => by simp only [map_add, smul_add])
      map_smul := fun i j hij V r x => by
        simp only [AddMonoidHom.mk'_apply, f.map_smul, smul_comm k r]
      naturality := fun i j hij V W q x => by
        simp only [AddMonoidHom.mk'_apply, map_nsmul, f.naturality]
        rfl
      isLinear := fun i j hij p V x b => by
        simp only [AddMonoidHom.mk'_apply]
        rw [f.isLinear i j hij p V x b, map_nsmul, AddMonoidHom.nsmul_apply] }

/-- The pointwise multiple of a local homomorphism by an integer. -/
instance : SMul ℤ (LocalHom K L n U) where
  smul k f :=
    { app := fun i j hij V => AddMonoidHom.mk' (fun x => k • f.app i j hij V x)
        (fun x y => by simp only [map_add, smul_add])
      map_smul := fun i j hij V r x => by
        simp only [AddMonoidHom.mk'_apply, f.map_smul, smul_comm k r]
      naturality := fun i j hij V W q x => by
        simp only [AddMonoidHom.mk'_apply, map_zsmul, f.naturality]
        rfl
      isLinear := fun i j hij p V x b => by
        simp only [AddMonoidHom.mk'_apply]
        rw [f.isLinear i j hij p V x b, map_zsmul, AddMonoidHom.zsmul_apply] }

/-- The zero local homomorphism takes every local section to zero. -/
@[simp] theorem zero_app' (i j : ℤ) (hij : i + n = j) (V : Over U)
    (x : (K.complex.X i).val.obj (op V.left)) :
    (0 : LocalHom K L n U).app i j hij V x = 0 := rfl

/-- The value of a sum of local homomorphisms is the sum of the values. -/
@[simp] theorem add_app (f g : LocalHom K L n U) (i j : ℤ) (hij : i + n = j) (V : Over U)
    (x : (K.complex.X i).val.obj (op V.left)) :
    (f + g).app i j hij V x = f.app i j hij V x + g.app i j hij V x := rfl

/-- The value of the negation of a local homomorphism is the negation of the value. -/
@[simp] theorem neg_app (f : LocalHom K L n U) (i j : ℤ) (hij : i + n = j) (V : Over U)
    (x : (K.complex.X i).val.obj (op V.left)) :
    (-f).app i j hij V x = -f.app i j hij V x := rfl

/-- The value of a difference of local homomorphisms is the difference of the values. -/
@[simp] theorem sub_app (f g : LocalHom K L n U) (i j : ℤ) (hij : i + n = j) (V : Over U)
    (x : (K.complex.X i).val.obj (op V.left)) :
    (f - g).app i j hij V x = f.app i j hij V x - g.app i j hij V x := rfl

/-- The value of `k • f`, for a natural number `k`, is `k` times the value of `f`. -/
@[simp] theorem nsmul_app (k : ℕ) (f : LocalHom K L n U) (i j : ℤ) (hij : i + n = j)
    (V : Over U) (x : (K.complex.X i).val.obj (op V.left)) :
    (k • f).app i j hij V x = k • f.app i j hij V x := rfl

/-- The value of `k • f`, for an integer `k`, is `k` times the value of `f`. -/
@[simp] theorem zsmul_app (k : ℤ) (f : LocalHom K L n U) (i j : ℤ) (hij : i + n = j)
    (V : Over U) (x : (K.complex.X i).val.obj (op V.left)) :
    (k • f).app i j hij V x = k • f.app i j hij V x := rfl

/-- The local homomorphisms of degree `n` over `U` form an additive commutative group under
pointwise operations. -/
instance : AddCommGroup (LocalHom K L n U) where
  add_assoc f g h := LocalHom.ext fun i j hij V x => add_assoc _ _ _
  zero_add f := LocalHom.ext fun i j hij V x => zero_add _
  add_zero f := LocalHom.ext fun i j hij V x => add_zero _
  add_comm f g := LocalHom.ext fun i j hij V x => add_comm _ _
  neg_add_cancel f := LocalHom.ext fun i j hij V x => neg_add_cancel _
  sub_eq_add_neg f g := LocalHom.ext fun i j hij V x => sub_eq_add_neg _ _
  nsmul k f := k • f
  zsmul k f := k • f
  nsmul_zero f := LocalHom.ext fun i j hij V x => zero_smul _ _
  nsmul_succ k f := LocalHom.ext fun i j hij V x => succ_nsmul _ _
  zsmul_zero' f := LocalHom.ext fun i j hij V x => zero_smul _ _
  zsmul_succ' k f := LocalHom.ext fun i j hij V x => by
    simp only [zsmul_app, add_app, Int.natCast_succ, add_smul, one_smul, natCast_zsmul]
  zsmul_neg' k f := LocalHom.ext fun i j hij V x => by
    simp only [zsmul_app, neg_app, negSucc_zsmul, natCast_zsmul]

/-! ### The module structure -/

variable [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)]

/-- Multiplication in a ring of sections of `R` is commutative. -/
theorem ring_mul_comm {U : Cᵒᵖ} (r r' : R.obj.obj U) : r * r' = r' * r :=
  Std.Commutative.comm r r'

/-- The action `(r f)(x) = r|_V f(x)` of a section `r` of `R` over `U` on a local homomorphism. -/
instance : SMul (R.obj.obj (op U)) (LocalHom K L n U) where
  smul r f :=
    { app := fun i j hij V => AddMonoidHom.mk'
        (fun x => R.obj.map V.hom.op r • f.app i j hij V x)
        (fun x y => by simp only [map_add, smul_add])
      map_smul := fun i j hij V r' x => by
        simp only [AddMonoidHom.mk'_apply, f.map_smul, smul_smul, ring_mul_comm]
      naturality := fun i j hij V W q x => by
        simp only [AddMonoidHom.mk'_apply]
        rw [PresheafOfModules.map_smul, f.naturality, ← Over.w q, op_comp, Functor.map_comp]
        rfl
      isLinear := fun i j hij p V x b => by
        simp only [AddMonoidHom.mk'_apply]
        rw [f.isLinear i j hij p V x b]
        exact ((L.mul j p).map_smul_left _ _ _ _).symm }

/-- The value of `r • f` over `V` is the restriction of `r` to `V` times the value of `f`. -/
@[simp] theorem smul_app (r : R.obj.obj (op U)) (f : LocalHom K L n U) (i j : ℤ)
    (hij : i + n = j) (V : Over U) (x : (K.complex.X i).val.obj (op V.left)) :
    (r • f).app i j hij V x = R.obj.map V.hom.op r • f.app i j hij V x := rfl

/-- The local homomorphisms of degree `n` over `U` form a module over the ring of sections of `R`
over `U`. -/
instance : Module (R.obj.obj (op U)) (LocalHom K L n U) where
  one_smul f := LocalHom.ext fun i j hij V x => by
    rw [smul_app, map_one, one_smul]
  mul_smul r r' f := LocalHom.ext fun i j hij V x => by
    rw [smul_app, smul_app, smul_app, map_mul, mul_smul]
  smul_zero r := LocalHom.ext fun i j hij V x => by
    rw [smul_app, zero_app']
    exact smul_zero _
  smul_add r f g := LocalHom.ext fun i j hij V x => by
    rw [smul_app, add_app, add_app, smul_app, smul_app, smul_add]
  add_smul r r' f := LocalHom.ext fun i j hij V x => by
    rw [smul_app, add_app, smul_app, smul_app, map_add, add_smul]
  zero_smul f := LocalHom.ext fun i j hij V x => by
    rw [smul_app, zero_app', map_zero, zero_smul]

/-- The module structure over the ring of sections at an object of `Cᵒᵖ`. -/
noncomputable instance instModuleUnop (U : Cᵒᵖ) : Module (R.obj.obj U) (LocalHom K L n U.unop) :=
  inferInstanceAs (Module (R.obj.obj (op U.unop)) (LocalHom K L n U.unop))

/-! ### Restriction -/

variable {U' U'' : C}

omit [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)] in
/-- The value of the restriction of `f` along `g : U' ⟶ U` over `V` is the value of `f` over
`V.hom ≫ g`. -/
@[simp] theorem restrict_app (g : U' ⟶ U) (f : LocalHom K L n U) (i j : ℤ) (hij : i + n = j)
    (V : Over U') (x : (K.complex.X i).val.obj (op V.left)) :
    (f.restrict g).app i j hij V x = f.app i j hij (Over.mk (V.hom ≫ g)) x := rfl

omit [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)] in
/-- Restriction of local homomorphisms is additive. -/
theorem restrict_add (g : U' ⟶ U) (f f' : LocalHom K L n U) :
    (f + f').restrict g = f.restrict g + f'.restrict g := rfl

/-- Restriction along `g` is semilinear over the restriction map `R(U) → R(U')`. -/
theorem restrict_smul (g : U' ⟶ U) (r : R.obj.obj (op U)) (f : LocalHom K L n U) :
    (r • f).restrict g = R.obj.map g.op r • f.restrict g :=
  LocalHom.ext fun i j hij V x => by
    rw [restrict_app, smul_app, smul_app, restrict_app]
    change (R.obj.map (g.op ≫ V.hom.op)) r • _ = _
    rw [Functor.map_comp]
    rfl

omit [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)] in
/-- Restriction along the identity is the identity. -/
theorem restrict_id (f : LocalHom K L n U) : f.restrict (𝟙 U) = f :=
  LocalHom.ext fun i j hij V x => by
    rw [restrict_app]
    exact LocalGradedHom.app_mk_congr f.toLocalGradedHom i j hij (Category.comp_id V.hom) x

omit [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)] in
/-- Restriction along a composite is the composite of the restrictions. -/
theorem restrict_comp (g : U' ⟶ U) (g' : U'' ⟶ U') (f : LocalHom K L n U) :
    f.restrict (g' ≫ g) = (f.restrict g).restrict g' :=
  LocalHom.ext fun i j hij V x => by
    rw [restrict_app, restrict_app, restrict_app]
    exact LocalGradedHom.app_mk_congr f.toLocalGradedHom i j hij
      (Category.assoc V.hom g' g).symm x

/-! ### Values over the slice site -/

omit [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)] in
/-- A local homomorphism is natural for the restriction from an object `V` of the slice site to an
object `W ⟶ V.left` mapping to it. -/
theorem map_app_eq (f : LocalHom K L n U) (i j : ℤ) (hij : i + n = j) (V : Over U) {W : C}
    (g : W ⟶ V.left) (x : (K.complex.X i).val.obj (op V.left)) :
    (L.complex.X j).val.map g.op (f.app i j hij V x) =
      f.app i j hij (Over.mk (g ≫ V.hom)) ((K.complex.X i).val.map g.op x) :=
  f.naturality i j hij (V := V) (W := Over.mk (g ≫ V.hom)) (Over.homMk g) x

omit [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)] in
/-- The value of a local homomorphism over `W ⟶ U` is the value of its restriction to `W` over the
terminal object of the slice site. -/
theorem app_mk_eq_restrict (f : LocalHom K L n U) (i j : ℤ) (hij : i + n = j) {W : C}
    (g : W ⟶ U) (y : (K.complex.X i).val.obj (op W)) :
    f.app i j hij (Over.mk g) y = (f.restrict g).app i j hij (Over.mk (𝟙 W)) y :=
  LocalGradedHom.app_mk_congr f.toLocalGradedHom i j hij (Category.id_comp g).symm y

end LocalHom

/-! ### The differential -/

namespace LocalHom

variable {K : DifferentialGradedModule.{t, a, z} A} {L : DifferentialGradedModule.{t, a, s} A}
  {n : ℤ} {U : C}

/-- The differential `d(f) = d_L ∘ f - (-1)^n f ∘ d_K` of a degree-`n` local homomorphism, a
degree-`(n + 1)` local homomorphism. -/
def diffAt (f : LocalHom K L n U) : LocalHom K L (n + 1) U where
  app i j hij V :=
    (homSections (L.complex.d (i + n) j) (op V.left)).comp (f.app i (i + n) rfl V) -
      (n.negOnePow : ℤ) • (f.app (i + 1) j (by omega) V).comp
        (homSections (K.complex.d i (i + 1)) (op V.left))
  map_smul i j hij V r x := by
    simp only [AddMonoidHom.sub_apply, AddMonoidHom.coe_comp, Function.comp_apply,
      AddMonoidHom.zsmul_apply, f.map_smul, homSections_smul, smul_sub, smul_comm _ r]
  naturality i j hij {V W} q x := by
    simp only [AddMonoidHom.sub_apply, AddMonoidHom.coe_comp, Function.comp_apply,
      AddMonoidHom.zsmul_apply]
    rw [map_sub_sections, map_zsmul_sections]
    simp only [homSections_naturality, f.naturality]
    rfl
  isLinear i j hij p V x b := by
    obtain rfl : j = i + n + 1 := by omega
    simp only [AddMonoidHom.sub_apply, AddMonoidHom.coe_comp, Function.comp_apply,
      AddMonoidHom.zsmul_apply, homSections_apply, map_sub, map_zsmul, AddMonoidHom.sub_apply,
      AddMonoidHom.zsmul_apply]
    rw [f.toLocalGradedHom.app_castHom_target (show i + n + p = i + p + n by omega) (by omega)
        (by omega) V,
      f.isLinear i (i + n) rfl p V x b,
      d_castHom_app L.complex (show i + n + p = i + p + n by omega)
        (show i + n + p + 1 = i + n + 1 + p by omega),
      L.leibniz_castHom (i + n) p (op V.left) (f.app i (i + n) rfl V x) b,
      K.leibniz_castHom i p (op V.left) x b]
    simp only [map_add, map_zsmul, castHom_castHom, castHom_self]
    rw [f.toLocalGradedHom.app_castHom_source (show i + 1 + p = i + p + 1 by omega) (by omega)
        (by omega) V,
      f.toLocalGradedHom.app_castHom_source (show i + (p + 1) = i + p + 1 by omega) (by omega)
        (by omega) V,
      f.isLinear (i + 1) (i + n + 1) (by omega) p V _ b,
      f.toLocalGradedHom.app_castHom_target (show i + n + (p + 1) = i + n + 1 + p by omega)
        (by omega) (by omega) V,
      f.isLinear i (i + n) rfl (p + 1) V x _]
    simp only [Int.negOnePow_add, Units.val_mul, mul_smul]
    rw [smul_add, smul_comm ((n.negOnePow : ℤˣ) : ℤ) ((i.negOnePow : ℤˣ) : ℤ)]
    abel

/-- The value of `d(f)` at `x` is `d_L (f x) - (-1)^n f (d_K x)`. -/
theorem diffAt_app (f : LocalHom K L n U) (i j : ℤ) (hij : i + (n + 1) = j) (V : Over U)
    (x : (K.complex.X i).val.obj (op V.left)) :
    f.diffAt.app i j hij V x =
      (L.complex.d (i + n) j).val.app (op V.left) (f.app i (i + n) rfl V x) -
        (n.negOnePow : ℤ) • f.app (i + 1) j (by omega) V
          ((K.complex.d i (i + 1)).val.app (op V.left) x) := rfl

/-- The differential of a local homomorphism is the value of the differential of the internal hom,
`SheafOfModules.localDiffApp`. -/
theorem diffAt_app_eq_localDiffApp (f : LocalHom K L n U) (i j : ℤ) (hij : i + (n + 1) = j)
    (V : Over U) (x : (K.complex.X i).val.obj (op V.left)) :
    f.diffAt.app i j hij V x = localDiffApp f.toLocalGradedHom (n + 1) i j hij V x := by
  rw [diffAt_app, localDiffApp_eq f.toLocalGradedHom (n + 1) i j (i + n) (i + 1) hij rfl
    (by omega), Int.negOnePow_succ, Units.val_neg, neg_smul, sub_eq_add_neg]

/-- The differential of local homomorphisms is additive. -/
theorem diffAt_add (f g : LocalHom K L n U) : (f + g).diffAt = f.diffAt + g.diffAt :=
  LocalHom.ext fun i j hij V x => by
    simp only [diffAt_app, add_app, map_add, smul_add]
    abel

/-- The differential commutes with restriction. -/
theorem diffAt_restrict {U' : C} (g : U' ⟶ U) (f : LocalHom K L n U) :
    (f.restrict g).diffAt = f.diffAt.restrict g := rfl

/-- The differential is linear over the ring of sections of `R`. -/
theorem diffAt_smul [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)] (r : R.obj.obj (op U))
    (f : LocalHom K L n U) : (r • f).diffAt = r • f.diffAt :=
  LocalHom.ext fun i j hij V x => by
    rw [diffAt_app, smul_app, smul_app, smul_app, diffAt_app, ← homSections_apply,
      homSections_smul, smul_sub, smul_comm (R.obj.map V.hom.op r)]
    rfl

/-- Two consecutive differentials of a complex of sheaves of modules compose to zero on local
sections. -/
theorem _root_.SheafOfModules.complex_d_d_app (Y : CochainComplex (SheafOfModules.{s} R) ℤ)
    (i j k : ℤ) (W : Cᵒᵖ) (y : (Y.X i).val.obj W) :
    (Y.d j k).val.app W ((Y.d i j).val.app W y) = 0 := by
  rw [← homSections_apply, ← homSections_apply, ← homSections_comp,
    homSections_congr (Y.d_comp_d i j k), homSections_zero]

/-- The differential of the internal hom squares to zero. -/
theorem diffAt_diffAt (f : LocalHom K L n U) : f.diffAt.diffAt = 0 :=
  LocalHom.ext fun i j hij V x => by
    have key : ∀ (q q' : ℤ) (hq : i + 1 + n = q) (hq' : i + 1 + n = q')
        (hqj : q + 1 = j) (hq'j : q' + 1 = j),
        (L.complex.d q j).val.app (op V.left) (f.app (i + 1) q hq V
          ((K.complex.d i (i + 1)).val.app (op V.left) x)) =
        (L.complex.d q' j).val.app (op V.left) (f.app (i + 1) q' hq' V
          ((K.complex.d i (i + 1)).val.app (op V.left) x)) := by
      intro q q' hq hq' _ _; subst hq; subst hq'; rfl
    rw [diffAt_app, diffAt_app, diffAt_app, zero_app', map_sub, map_zsmul,
      complex_d_d_app, complex_d_d_app, map_zero, smul_zero, sub_zero,
      key (i + (n + 1)) (i + 1 + n) (by omega) rfl (by omega) (by omega),
      Int.negOnePow_succ, Units.val_neg, neg_smul]
    abel

/-- The differential of the internal hom, from degree `n` to a degree `m = n + 1`. -/
def diffTo (f : LocalHom K L n U) (m : ℤ) (hm : n + 1 = m) : LocalHom K L m U :=
  hm ▸ f.diffAt

/-- The value of `SheafOfModules.LocalHom.diffTo` is `SheafOfModules.localDiffApp`. -/
theorem diffTo_app (f : LocalHom K L n U) (m : ℤ) (hm : n + 1 = m) (i j : ℤ) (hij : i + m = j)
    (V : Over U) (x : (K.complex.X i).val.obj (op V.left)) :
    (f.diffTo m hm).app i j hij V x = localDiffApp f.toLocalGradedHom m i j hij V x := by
  subst hm
  exact diffAt_app_eq_localDiffApp f i j hij V x

/-- The member of a family `φ` indexed by a sieve at `f'` is the restriction of the member at `f`
along `g` when `g ≫ f = f'`. -/
private theorem family_eq_restrict {X : C} (S : Sieve X)
    (φ : ∀ ⦃W : C⦄ (f : W ⟶ X), S f → LocalHom K L n W)
    (hφ : ∀ ⦃W W' : C⦄ (f : W ⟶ X) (g : W' ⟶ W) (hf : S f),
      φ (g ≫ f) (S.downward_closed hf g) = (φ f hf).restrict g)
    {W W' : C} {f : W ⟶ X} {f' : W' ⟶ X} (g : W' ⟶ W) (e : g ≫ f = f') (hf : S f) (hf' : S f') :
    φ f' hf' = (φ f hf).restrict g := by
  subst e
  exact hφ f g hf

end LocalHom

variable [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)]

/-- The presheaf of `R`-modules `U ↦ SheafHom^n_A(K, L)(U)` of degree-`n` local homomorphisms. -/
noncomputable abbrev localHomPresheaf (K : DifferentialGradedModule.{t, a, z} A)
    (L : DifferentialGradedModule.{t, a, s} A) (n : ℤ) :
    PresheafOfModules.{max u v z s} R.obj where
  obj U := ModuleCat.of (R.obj.obj (op U.unop)) (LocalHom K L n U.unop)
  map {U U'} g := ModuleCat.ofHom
      (Y := (ModuleCat.restrictScalars (R.obj.map g).hom).obj
        (ModuleCat.of (R.obj.obj (op U'.unop)) (LocalHom K L n U'.unop)))
    { toFun := fun f => f.restrict g.unop
      map_add' := fun f f' => LocalHom.restrict_add g.unop f f'
      map_smul' := fun r f => LocalHom.restrict_smul g.unop r f }
  map_id U := by
    ext f
    exact LocalHom.restrict_id f
  map_comp g g' := by
    ext f
    exact LocalHom.restrict_comp g.unop g'.unop f

/-- The restriction map of `SheafOfModules.localHomPresheaf` is restriction of local
homomorphisms. -/
theorem localHomPresheaf_map_apply (K : DifferentialGradedModule.{t, a, z} A)
    (L : DifferentialGradedModule.{t, a, s} A) (n : ℤ) {U U' : Cᵒᵖ} (g : U ⟶ U')
    (f : LocalHom K L n U.unop) :
    (localHomPresheaf K L n).map g f = f.restrict g.unop := rfl


/-! ### The sheaf condition -/

omit [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)] in
/-- Restriction along an identity is the identity, on local sections of a sheaf of modules. -/
theorem sheafSectionsMap_id_apply (F : SheafOfModules.{s} R) {U : Cᵒᵖ} (x : F.val.obj U) :
    F.val.map (𝟙 U) x = x := by
  rw [F.val.map_id]; rfl

omit [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)] in
/-- The presheaf of local sections of a sheaf of modules, as a presheaf of types, is a sheaf. -/
theorem sheafSections_isSheafForget (F : SheafOfModules.{s} R) :
    Presieve.IsSheaf J (F.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{s}) :=
  (isSheaf_iff_isSheaf_of_type _ _).mp (Presheaf.isSheaf_comp_of_isSheaf _ _ _ F.isSheaf)

namespace LocalHom

section Glue

variable {K : DifferentialGradedModule.{t, a, z} A} {L : DifferentialGradedModule.{t, a, s} A}
  {n : ℤ} {X : C} (S : Sieve X) (hS : S ∈ J X)
  (φ : ∀ ⦃W : C⦄ (f : W ⟶ X), S f → LocalHom K L n W)
  (hφ : ∀ ⦃W W' : C⦄ (f : W ⟶ X) (g : W' ⟶ W) (hf : S f),
    φ (g ≫ f) (S.downward_closed hf g) = (φ f hf).restrict g)

omit [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)] in
/-- Members of the family `φ` at equal morphisms are equal. -/
theorem glue_congr {W : C} {f f' : W ⟶ X} (e : f = f') (hf : S f) (hf' : S f') :
    φ f hf = φ f' hf' := by
  subst e; rfl

/-- The family of local sections of `L` over the sieve `S` pulled back to `V`, whose gluing is the
value of the glued local homomorphism at a local section `x` of `K` over `V`. -/
noncomputable def glueFamily (i j : ℤ) (hij : i + n = j) (V : Over X)
    (x : (K.complex.X i).val.obj (op V.left)) :
    Presieve.FamilyOfElements ((L.complex.X j).val.presheaf ⋙ CategoryTheory.forget _)
      (S.pullback V.hom).arrows :=
  fun W g hg => (φ (g ≫ V.hom) hg).app i j hij (Over.mk (𝟙 W))
    ((K.complex.X i).val.map g.op x)

omit [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)] in
include hφ in
/-- The family `SheafOfModules.LocalHom.glueFamily` is compatible. -/
theorem glueFamily_compatible (i j : ℤ) (hij : i + n = j) (V : Over X)
    (x : (K.complex.X i).val.obj (op V.left)) :
    (glueFamily S φ i j hij V x).Compatible := by
  rw [Presieve.compatible_iff_sieveCompatible]
  intro W W' g h hg
  change (φ ((h ≫ g) ≫ V.hom) ((S.pullback V.hom).downward_closed hg h)).app i j hij
      (Over.mk (𝟙 W')) ((K.complex.X i).val.map (h ≫ g).op x) =
    (L.complex.X j).val.map h.op ((φ (g ≫ V.hom) hg).app i j hij (Over.mk (𝟙 W))
      ((K.complex.X i).val.map g.op x))
  rw [family_eq_restrict S φ hφ h (Category.assoc h g V.hom).symm hg
    ((S.pullback V.hom).downward_closed hg h)]
  refine Eq.trans ?_ (map_app_eq (φ (g ≫ V.hom) hg) i j hij (Over.mk (𝟙 W)) h _).symm
  have e2 : (K.complex.X i).val.map (h ≫ g).op x =
      (K.complex.X i).val.map h.op ((K.complex.X i).val.map g.op x) := by
    rw [op_comp, PresheafOfModules.map_comp_apply]
  change (φ (g ≫ V.hom) hg).app i j hij (Over.mk (𝟙 W' ≫ h))
      ((K.complex.X i).val.map (h ≫ g).op x) = _
  rw [e2]
  exact LocalGradedHom.app_mk_congr _ i j hij
    ((Category.id_comp h).trans (Category.comp_id h).symm) _

/-- The value of the glued local homomorphism at a local section `x` of `K` over `V`. -/
noncomputable def glueApp (i j : ℤ) (hij : i + n = j) (V : Over X)
    (x : (K.complex.X i).val.obj (op V.left)) : (L.complex.X j).val.obj (op V.left) :=
  (sheafSections_isSheafForget (L.complex.X j) _ (J.pullback_stable V.hom hS)).amalgamate
    (glueFamily S φ i j hij V x) (glueFamily_compatible S φ hφ i j hij V x)

omit [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)] in
/-- The restriction of `SheafOfModules.LocalHom.glueApp` along `g : W ⟶ V.left` with `g ≫ V.hom`
in `S` is the value of the member of the family at `g ≫ V.hom`. -/
theorem map_glueApp (i j : ℤ) (hij : i + n = j) (V : Over X)
    (x : (K.complex.X i).val.obj (op V.left)) {W : C} (g : W ⟶ V.left) (hg : S (g ≫ V.hom)) :
    (L.complex.X j).val.map g.op (glueApp S hS φ hφ i j hij V x) =
      (φ (g ≫ V.hom) hg).app i j hij (Over.mk (𝟙 W)) ((K.complex.X i).val.map g.op x) :=
  (sheafSections_isSheafForget (L.complex.X j) _ (J.pullback_stable V.hom hS)).valid_glue
    (glueFamily_compatible S φ hφ i j hij V x) g hg

omit [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)] in
include hS in
/-- Two local sections of `L` over `V` agreeing after restriction to every member of the pullback
of the covering sieve `S` are equal. -/
theorem glue_ext (j : ℤ) (V : Over X) {y y' : (L.complex.X j).val.obj (op V.left)}
    (h : ∀ ⦃W : C⦄ (g : W ⟶ V.left), S (g ≫ V.hom) →
      (L.complex.X j).val.map g.op y = (L.complex.X j).val.map g.op y') :
    y = y' :=
  (sheafSections_isSheafForget (L.complex.X j) _ (J.pullback_stable V.hom hS)).isSeparatedFor.ext
    fun _ g hg => h g hg

/-- The local homomorphism glued from a compatible family over a covering sieve. -/
noncomputable def glue : LocalHom K L n X where
  app i j hij V := AddMonoidHom.mk' (glueApp S hS φ hφ i j hij V) (fun x y =>
    glue_ext S hS j V fun W g hg => by
      rw [map_add, map_glueApp S hS φ hφ i j hij V _ g hg,
        map_glueApp S hS φ hφ i j hij V _ g hg, map_glueApp S hS φ hφ i j hij V _ g hg,
        map_add]
      exact ((φ (g ≫ V.hom) hg).app i j hij (Over.mk (𝟙 W))).map_add _ _)
  map_smul i j hij V r x := glue_ext S hS j V fun W g hg => by
    change (L.complex.X j).val.map g.op (glueApp S hS φ hφ i j hij V (r • x)) =
      (L.complex.X j).val.map g.op (r • glueApp S hS φ hφ i j hij V x)
    rw [map_glueApp S hS φ hφ i j hij V _ g hg, PresheafOfModules.map_smul,
      PresheafOfModules.map_smul, map_glueApp S hS φ hφ i j hij V _ g hg]
    exact (φ (g ≫ V.hom) hg).map_smul i j hij (Over.mk (𝟙 W)) _ _
  naturality i j hij V W q x := glue_ext S hS j W fun W' g hg => by
    have hg' : S ((g ≫ q.left) ≫ V.hom) := by
      rw [Category.assoc, Over.w q]; exact hg
    change (L.complex.X j).val.map g.op ((L.complex.X j).val.map q.left.op
        (glueApp S hS φ hφ i j hij V x)) =
      (L.complex.X j).val.map g.op (glueApp S hS φ hφ i j hij W
        ((K.complex.X i).val.map q.left.op x))
    have e : φ ((g ≫ q.left) ≫ V.hom) hg' = φ (g ≫ W.hom) hg :=
      glue_congr S φ (by rw [Category.assoc, Over.w q]) hg' hg
    rw [← PresheafOfModules.map_comp_apply, ← op_comp, map_glueApp S hS φ hφ i j hij V x _ hg']
    refine Eq.trans ?_ (map_glueApp S hS φ hφ i j hij W _ g hg).symm
    rw [e, op_comp, PresheafOfModules.map_comp_apply]
  isLinear i j hij b V x c := glue_ext S hS (j + b) V fun W g hg => by
    change (L.complex.X (j + b)).val.map g.op (glueApp S hS φ hφ (i + b) (j + b) (by omega) V
        ((K.mul i b).app (op V.left) x c)) =
      (L.complex.X (j + b)).val.map g.op
        ((L.mul j b).app (op V.left) (glueApp S hS φ hφ i j hij V x) c)
    rw [map_glueApp S hS φ hφ (i + b) (j + b) (by omega) V _ g hg, (K.mul i b).naturality,
      (L.mul j b).naturality, map_glueApp S hS φ hφ i j hij V _ g hg]
    exact (φ (g ≫ V.hom) hg).isLinear i j hij b (Over.mk (𝟙 W)) _ _

omit [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)] in
/-- The value of the glued local homomorphism is `SheafOfModules.LocalHom.glueApp`. -/
theorem glue_app (i j : ℤ) (hij : i + n = j) (V : Over X)
    (x : (K.complex.X i).val.obj (op V.left)) :
    (glue S hS φ hφ).app i j hij V x = glueApp S hS φ hφ i j hij V x := rfl

omit [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)] in
/-- The glued local homomorphism restricts to the members of the family. -/
theorem restrict_glue {W : C} (f : W ⟶ X) (hf : S f) : (glue S hS φ hφ).restrict f = φ f hf :=
  LocalHom.ext fun i j hij V x => by
    rw [restrict_app, glue_app]
    have hm : S (𝟙 V.left ≫ (Over.mk (V.hom ≫ f)).hom) := by
      rw [Category.id_comp]; exact S.downward_closed hf V.hom
    have h := map_glueApp S hS φ hφ i j hij (Over.mk (V.hom ≫ f)) x (𝟙 V.left) hm
    rw [family_eq_restrict S φ hφ (f' := 𝟙 V.left ≫ (Over.mk (V.hom ≫ f)).hom) V.hom
      (Category.id_comp _).symm hf hm] at h
    refine (sheafSectionsMap_id_apply _ _).symm.trans (h.trans ?_)
    refine (congrArg ((φ f hf).app i j hij (Over.mk (𝟙 V.left ≫ V.hom)))
      (sheafSectionsMap_id_apply (K.complex.X i) x)).trans ?_
    exact LocalGradedHom.app_mk_congr _ i j hij (Category.id_comp V.hom) x

omit [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)] in
/-- A local homomorphism restricting to the members of the family is the glued one. -/
theorem eq_glue (f : LocalHom K L n X)
    (hf : ∀ ⦃W : C⦄ (g : W ⟶ X) (hg : S g), f.restrict g = φ g hg) :
    f = glue S hS φ hφ :=
  LocalHom.ext fun i j hij V x => glue_ext S hS j V fun W g hg => by
    refine (map_app_eq f i j hij V g x).trans (Eq.trans ?_
      (map_glueApp S hS φ hφ i j hij V x g hg).symm)
    refine (app_mk_eq_restrict f i j hij (g ≫ V.hom) _).trans ?_
    rw [hf _ hg]

end Glue

end LocalHom

/-- **The local homomorphisms form a sheaf**: the presheaf `U ↦ SheafHom^n_A(K, L)(U)` satisfies
the sheaf condition. -/
theorem localHomPresheaf_isSheaf (K : DifferentialGradedModule.{t, a, z} A)
    (L : DifferentialGradedModule.{t, a, s} A) (n : ℤ) :
    Presheaf.IsSheaf J (localHomPresheaf K L n).presheaf := by
  refine Presheaf.isSheaf_of_isSheaf_comp J _
    (CategoryTheory.forget AddCommGrpCat.{max u v z s}) ?_
  rw [isSheaf_iff_isSheaf_of_type]
  intro X S hS x hx
  let φ : ∀ ⦃W : C⦄ (f : W ⟶ X), S f → LocalHom K L n W := fun W f hf => x f hf
  have hφ : ∀ ⦃W W' : C⦄ (f : W ⟶ X) (g : W' ⟶ W) (hf : S f),
      φ (g ≫ f) (S.downward_closed hf g) = (φ f hf).restrict g :=
    fun W W' f g hf => hx.to_sieveCompatible f g hf
  exact ⟨LocalHom.glue S hS φ hφ, fun W f hf => LocalHom.restrict_glue S hS φ hφ f hf,
    fun t ht => LocalHom.eq_glue S hS φ hφ t fun W g hg => ht g hg⟩

/-- The degree-`n` part `SheafHom^n_A(K, L)` of the internal hom, as a sheaf of `R`-modules. -/
noncomputable abbrev localHomSheaf (K : DifferentialGradedModule.{t, a, z} A)
    (L : DifferentialGradedModule.{t, a, s} A) (n : ℤ) : SheafOfModules.{max u v z s} R where
  val := localHomPresheaf K L n
  isSheaf := localHomPresheaf_isSheaf K L n

/-- The module of sections of `SheafOfModules.localHomSheaf` over `U` is the module of local
homomorphisms over `U`. -/
theorem localHomSheaf_obj (K : DifferentialGradedModule.{t, a, z} A)
    (L : DifferentialGradedModule.{t, a, s} A) (n : ℤ) (U : C) :
    (localHomSheaf K L n).val.obj (op U) = ModuleCat.of (R.obj.obj (op U)) (LocalHom K L n U) :=
  rfl

/-- The differential `SheafHom^n_A(K, L) ⟶ SheafHom^{n + 1}_A(K, L)` of the internal hom, as a
morphism of sheaves of modules. -/
noncomputable def localHomDiff (K : DifferentialGradedModule.{t, a, z} A)
    (L : DifferentialGradedModule.{t, a, s} A) (n : ℤ) :
    localHomSheaf K L n ⟶ localHomSheaf K L (n + 1) where
  val :=
    { app := fun U => ModuleCat.ofHom
        { toFun := fun f => LocalHom.diffAt (U := U.unop) f
          map_add' := fun f g => LocalHom.diffAt_add f g
          map_smul' := fun r f => LocalHom.diffAt_smul r f }
      naturality := fun {_ _} g =>
        ModuleCat.hom_ext (LinearMap.ext fun f => LocalHom.diffAt_restrict g.unop f) }

/-- On sections over `U`, `SheafOfModules.localHomDiff` is the differential
`SheafOfModules.LocalHom.diffAt`. -/
theorem localHomDiff_app (K : DifferentialGradedModule.{t, a, z} A)
    (L : DifferentialGradedModule.{t, a, s} A) (n : ℤ) (U : C) (f : LocalHom K L n U) :
    (localHomDiff K L n).val.app (op U) f = f.diffAt := rfl

/-- **The internal hom `SheafHom^dg_A(K, L)`**, as a complex of sheaves of `R`-modules: in degree
`n` the sheaf of degree-`n` local homomorphisms `K|_U → L|_U`, with differential
`d(f) = d_L ∘ f - (-1)^n f ∘ d_K`. -/
noncomputable abbrev sheafHomComplex (K : DifferentialGradedModule.{t, a, z} A)
    (L : DifferentialGradedModule.{t, a, s} A) :
    CochainComplex (SheafOfModules.{max u v z s} R) ℤ where
  X n := localHomSheaf K L n
  d n m := if h : n + 1 = m then
      localHomDiff K L n ≫ eqToHom (congrArg (localHomSheaf K L) h) else 0
  shape n m h := dite_eq_right h
  d_comp_d' n m l h₁ h₂ := by
    change n + 1 = m at h₁
    change m + 1 = l at h₂
    subst h₁ h₂
    simp only [dite_eq_left, eqToHom_refl, Category.comp_id]
    exact hom_ext_sections fun U f => LocalHom.diffAt_diffAt (U := U.unop) f

/-- The degree-`n` term of `SheafOfModules.sheafHomComplex` is `SheafOfModules.localHomSheaf`. -/
theorem sheafHomComplex_X (K : DifferentialGradedModule.{t, a, z} A)
    (L : DifferentialGradedModule.{t, a, s} A) (n : ℤ) :
    (sheafHomComplex K L).X n = localHomSheaf K L n := rfl

/-- The differential of `SheafOfModules.sheafHomComplex` from degree `n` to degree `n + 1` is
`SheafOfModules.localHomDiff`. -/
theorem sheafHomComplex_d_self (K : DifferentialGradedModule.{t, a, z} A)
    (L : DifferentialGradedModule.{t, a, s} A) (n : ℤ) :
    (sheafHomComplex K L).d n (n + 1) = localHomDiff K L n := by
  simp only [dite_eq_left, eqToHom_refl, Category.comp_id]

/-- **The constructed complex is the internal hom**: its sections are the local homomorphisms,
additively, `R`-linearly and compatibly with restriction, and its differential is
`SheafOfModules.localDiffApp`. -/
noncomputable def isInternalHom_sheafHomComplex (K : DifferentialGradedModule.{t, a, z} A)
    (L : DifferentialGradedModule.{t, a, s} A) :
    IsInternalHom K L (sheafHomComplex K L) where
  sectionsEquiv n U := Equiv.refl _
  sectionsEquiv_add _ _ _ _ _ _ _ _ _ := rfl
  sectionsEquiv_smul _ _ _ _ _ _ _ _ _ := rfl
  sectionsEquiv_naturality _ _ _ _ _ _ _ _ _ := rfl
  sectionsEquiv_d n m U p i j hij V x := by
    by_cases h : n + 1 = m
    · subst h
      rw [sheafHomComplex_d_self]
      exact LocalHom.diffAt_app_eq_localDiffApp p i j hij V x
    · rw [(sheafHomComplex K L).shape n m h, localDiffApp_of_ne _ m i j hij
        (fun h' => h h'.symm) V x]
      rfl

end SheafOfModules
