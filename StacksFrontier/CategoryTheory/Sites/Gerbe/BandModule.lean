module

public import StacksFrontier.CategoryTheory.Sites.Gerbe.Defs
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.PullbackFiberHom
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Sites.Sheaf

/-!
# Descending module structures on automorphism groups to the band of a gerbe

Let `p : 𝒮 ⥤ 𝒞` be a fibred category over a site `(𝒞, J)`, locally nonempty, and `𝒢` a sheaf of
groups on `𝒞` *banding* `p`: for every object `x` of a fibre `𝒮_U` a bijection
`Θ_x : 𝒢(U) ≃ Aut(x)`, multiplicative, carried to conjugation by isomorphisms of the fibre, and
carried to the pullback of automorphisms by the restriction maps of `𝒢`. Let `R` be a presheaf of
rings on `𝒞` and suppose that every `Aut(x)`, `x ∈ 𝒮_U`, carries an `R(U)`-module structure
(addition being composition) such that conjugation by isomorphisms of the fibre is linear and
pullback of automorphisms along `g : V ⟶ U` is semilinear over `R(g)`. If any two objects of a
fibre are locally isomorphic, then these module structures descend to `𝒢`: there is a unique
multiplication `R(U) × 𝒢(U) ⟶ 𝒢(U)` read by every `Θ_x` as the given one, it makes `𝒢` a
presheaf of `R`-modules (`CategoryTheory.Functor.exists_bandSmul`).

## References

* [Stacks Project, Tag 0CKG](https://stacks.math.columbia.edu/tag/0CKG)
* [Stacks Project, Tag 0CJY](https://stacks.math.columbia.edu/tag/0CJY)
* [Stacks Project, Tag 04TP](https://stacks.math.columbia.edu/tag/04TP)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe w w' v₁ u₁ v₂ u₂

namespace CategoryTheory.Functor

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒮 : Type u₂} [Category.{v₂} 𝒮]
  (p : 𝒮 ⥤ 𝒞) [p.IsPreFibered] (J : GrothendieckTopology 𝒞)
  (𝒢 : Sheaf J CommGrpCat.{w}) (R : 𝒞ᵒᵖ ⥤ RingCat.{w'})
  (Θ : ∀ (U : 𝒞) (x : p.Fiber U), 𝒢.obj.obj (op U) ≃ (x ⟶ x))
  (smul : ∀ (U : 𝒞) (x : p.Fiber U), R.obj (op U) → (x ⟶ x) → (x ⟶ x))

/-- The candidate product over a frame: `r · a` read through `Θ_y` over `g : V ⟶ U` and the
object `y` of the fibre over `V`. -/
def bandSmulAt {U V : 𝒞} (g : V ⟶ U) (y : p.Fiber V) (r : R.obj (op U)) (a : 𝒢.obj.obj (op U)) :
    𝒢.obj.obj (op V) :=
  (Θ V y).symm (smul V y (R.map g.op r) (Θ V y (𝒢.obj.map g.op a)))

omit [p.IsPreFibered] in
/-- `Θ_y` reads the candidate product over the frame `(g, y)` as the given product on `Aut(y)`. -/
theorem Θ_bandSmulAt {U V : 𝒞} (g : V ⟶ U) (y : p.Fiber V) (r : R.obj (op U))
    (a : 𝒢.obj.obj (op U)) :
    Θ V y (bandSmulAt p J 𝒢 R Θ smul g y r a) =
      smul V y (R.map g.op r) (Θ V y (𝒢.obj.map g.op a)) :=
  (Θ V y).apply_symm_apply _

variable {p J 𝒢 R Θ smul}

section Descent

variable
  (hΘconj : ∀ (U : 𝒞) (x y : p.Fiber U) (φ : x ≅ y) (a : 𝒢.obj.obj (op U)),
    Θ U y a = φ.inv ≫ Θ U x a ≫ φ.hom)
  (hΘres : ∀ (U V : 𝒞) (g : V ⟶ U) (x : p.Fiber U) (a : 𝒢.obj.obj (op U)),
    Θ V (pullbackFiber p x g) (𝒢.obj.map g.op a) = pullbackFiberHom (Θ U x a) g)
  (hconj : ∀ (U : 𝒞) (x y : p.Fiber U) (φ : x ≅ y) (r : R.obj (op U)) (a : x ⟶ x),
    smul U y r (φ.inv ≫ a ≫ φ.hom) = φ.inv ≫ smul U x r a ≫ φ.hom)
  (hpull : ∀ (U V : 𝒞) (g : V ⟶ U) (x : p.Fiber U) (r : R.obj (op U)) (a : x ⟶ x),
    pullbackFiberHom (smul U x r a) g = smul V (pullbackFiber p x g) (R.map g.op r)
      (pullbackFiberHom a g))
  (hsh : Presieve.IsSheaf J (𝒢.obj ⋙ forget CommGrpCat.{w}))
  (hne : p.LocallyNonempty J)
  (hlc : ∀ (U : 𝒞) (x y : p.Fiber U), ∃ S ∈ J U, ∀ ⦃V : 𝒞⦄ (f : V ⟶ U), S f →
    Nonempty (pullbackFiber p x f ≅ pullbackFiber p y f))

/-- Restricting a section of `𝒢` along `g` and then along `k` is restricting it along `k ≫ g`. -/
private theorem map_comp_apply_eq' {U V Z : 𝒞} (g : V ⟶ U) (k : Z ⟶ V) (b : 𝒢.obj.obj (op U)) :
    (𝒢.obj.map k.op) ((𝒢.obj.map g.op) b) = (𝒢.obj.map (k ≫ g).op) b := by
  rw [op_comp, Functor.map_comp]
  rfl

include hΘres hpull in
/-- The candidate products restrict to candidate products. -/
theorem map_bandSmulAt {U V Z : 𝒞} (g : V ⟶ U) (y : p.Fiber V) (h : Z ⟶ V) (r : R.obj (op U))
    (a : 𝒢.obj.obj (op U)) :
    𝒢.obj.map h.op (bandSmulAt p J 𝒢 R Θ smul g y r a) =
      bandSmulAt p J 𝒢 R Θ smul (h ≫ g) (pullbackFiber p y h) r a := by
  apply (Θ Z (pullbackFiber p y h)).injective
  rw [Θ_bandSmulAt, hΘres, Θ_bandSmulAt, hpull, ← hΘres, op_comp, Functor.map_comp,
    Functor.map_comp]
  rfl

omit [p.IsPreFibered] in
include hΘconj hconj in
/-- Isomorphic frames give the same candidate product. -/
theorem bandSmulAt_eq_of_iso {U V : 𝒞} (g : V ⟶ U) {y y' : p.Fiber V} (φ : y ≅ y')
    (r : R.obj (op U)) (a : 𝒢.obj.obj (op U)) :
    bandSmulAt p J 𝒢 R Θ smul g y r a = bandSmulAt p J 𝒢 R Θ smul g y' r a := by
  apply (Θ V y').injective
  rw [hΘconj V y y' φ (bandSmulAt p J 𝒢 R Θ smul g y r a), Θ_bandSmulAt, Θ_bandSmulAt,
    hΘconj V y y' φ (𝒢.obj.map g.op a), hconj]

include hΘres hpull hΘconj hconj hlc hsh in
/-- The candidate product does not depend on the frame, the frames being locally isomorphic and
`𝒢` separated. -/
theorem bandSmulAt_eq {U V : 𝒞} (g : V ⟶ U) (y y' : p.Fiber V) (r : R.obj (op U))
    (a : 𝒢.obj.obj (op U)) :
    bandSmulAt p J 𝒢 R Θ smul g y r a = bandSmulAt p J 𝒢 R Θ smul g y' r a := by
  obtain ⟨T, hT, hiso⟩ := hlc V y y'
  refine (hsh T hT).isSeparatedFor.ext fun Z k hk => ?_
  change 𝒢.obj.map k.op _ = 𝒢.obj.map k.op _
  rw [map_bandSmulAt hΘres hpull, map_bandSmulAt hΘres hpull]
  exact bandSmulAt_eq_of_iso hΘconj hconj _ (hiso k hk).some r a

omit [p.IsPreFibered] in
include hne hsh in
/-- Two sections of `𝒢` read alike by every frame over every object over `U` are equal. -/
theorem eq_of_forall_Θ_eq {U : 𝒞} {b b' : 𝒢.obj.obj (op U)}
    (h : ∀ (V : 𝒞) (g : V ⟶ U) (y : p.Fiber V),
      Θ V y (𝒢.obj.map g.op b) = Θ V y (𝒢.obj.map g.op b')) : b = b' := by
  obtain ⟨S, hS, hne'⟩ := hne U
  exact (hsh S hS).isSeparatedFor.ext fun V g hg =>
    (Θ V (hne' g hg).some).injective (h V g (hne' g hg).some)

include hΘres hpull hΘconj hconj hlc hne hsh in
/-- There is a section of `𝒢` over `U` whose restriction along every `g : V ⟶ U` is the
candidate product over every frame `(g, y)`. -/
theorem exists_bandSmul_spec {U : 𝒞} (r : R.obj (op U)) (a : 𝒢.obj.obj (op U)) :
    ∃ b : 𝒢.obj.obj (op U), ∀ (V : 𝒞) (g : V ⟶ U) (y : p.Fiber V),
      𝒢.obj.map g.op b = bandSmulAt p J 𝒢 R Θ smul g y r a := by
  classical
  obtain ⟨S, hS, hne'⟩ := hne U
  let fam : Presieve.FamilyOfElements (𝒢.obj ⋙ forget CommGrpCat.{w}) S.arrows :=
    fun V g hg => bandSmulAt p J 𝒢 R Θ smul g (hne' g hg).some r a
  have hfam : fam.Compatible := by
    intro Z₁ Z₂ Z h₁ h₂ g₁ g₂ hg₁ hg₂ hcomm
    change 𝒢.obj.map h₁.op (fam g₁ hg₁) = 𝒢.obj.map h₂.op (fam g₂ hg₂)
    simp only [fam]
    rw [map_bandSmulAt hΘres hpull, map_bandSmulAt hΘres hpull]
    have key : ∀ (k k' : Z ⟶ U) (hk : k = k') (y y' : p.Fiber Z),
        bandSmulAt p J 𝒢 R Θ smul k y r a = bandSmulAt p J 𝒢 R Θ smul k' y' r a := by
      rintro k _ rfl y y'
      exact bandSmulAt_eq hΘconj hΘres hconj hpull hsh hlc k y y' r a
    exact key _ _ hcomm _ _
  refine ⟨(hsh S hS).amalgamate fam hfam, fun V g y => ?_⟩
  refine (hsh _ (J.pullback_stable g hS)).isSeparatedFor.ext fun Z k hk => ?_
  change 𝒢.obj.map k.op (𝒢.obj.map g.op _) = 𝒢.obj.map k.op _
  rw [map_comp_apply_eq', map_bandSmulAt hΘres hpull]
  have hk' : S.arrows (k ≫ g) := hk
  refine ((hsh S hS).valid_glue hfam (k ≫ g) hk').trans ?_
  exact bandSmulAt_eq hΘconj hΘres hconj hpull hsh hlc _ _ _ r a

end Descent

section Module

variable
  (hΘmul : ∀ (U : 𝒞) (x : p.Fiber U) (a b : 𝒢.obj.obj (op U)), Θ U x (a * b) = Θ U x a ≫ Θ U x b)
  (hΘconj : ∀ (U : 𝒞) (x y : p.Fiber U) (φ : x ≅ y) (a : 𝒢.obj.obj (op U)),
    Θ U y a = φ.inv ≫ Θ U x a ≫ φ.hom)
  (hΘres : ∀ (U V : 𝒞) (g : V ⟶ U) (x : p.Fiber U) (a : 𝒢.obj.obj (op U)),
    Θ V (pullbackFiber p x g) (𝒢.obj.map g.op a) = pullbackFiberHom (Θ U x a) g)
  (hcomp : ∀ (U : 𝒞) (x : p.Fiber U) (r : R.obj (op U)) (a b : x ⟶ x),
    smul U x r (a ≫ b) = smul U x r a ≫ smul U x r b)
  (hid : ∀ (U : 𝒞) (x : p.Fiber U) (r : R.obj (op U)), smul U x r (𝟙 x) = 𝟙 x)
  (hadd : ∀ (U : 𝒞) (x : p.Fiber U) (r s : R.obj (op U)) (a : x ⟶ x),
    smul U x (r + s) a = smul U x r a ≫ smul U x s a)
  (hzero : ∀ (U : 𝒞) (x : p.Fiber U) (a : x ⟶ x), smul U x 0 a = 𝟙 x)
  (hone : ∀ (U : 𝒞) (x : p.Fiber U) (a : x ⟶ x), smul U x 1 a = a)
  (hmul : ∀ (U : 𝒞) (x : p.Fiber U) (r s : R.obj (op U)) (a : x ⟶ x),
    smul U x (r * s) a = smul U x r (smul U x s a))
  (hconj : ∀ (U : 𝒞) (x y : p.Fiber U) (φ : x ≅ y) (r : R.obj (op U)) (a : x ⟶ x),
    smul U y r (φ.inv ≫ a ≫ φ.hom) = φ.inv ≫ smul U x r a ≫ φ.hom)
  (hpull : ∀ (U V : 𝒞) (g : V ⟶ U) (x : p.Fiber U) (r : R.obj (op U)) (a : x ⟶ x),
    pullbackFiberHom (smul U x r a) g = smul V (pullbackFiber p x g) (R.map g.op r)
      (pullbackFiberHom a g))
  (hsh : Presieve.IsSheaf J (𝒢.obj ⋙ forget CommGrpCat.{w}))
  (hne : p.LocallyNonempty J)
  (hlc : ∀ (U : 𝒞) (x y : p.Fiber U), ∃ S ∈ J U, ∀ ⦃V : 𝒞⦄ (f : V ⟶ U), S f →
    Nonempty (pullbackFiber p x f ≅ pullbackFiber p y f))

omit [p.IsPreFibered] in
include hΘmul in
/-- A multiplicative bijection `Θ_x` sends the unit of `𝒢(U)` to the identity of `x`. -/
theorem Θ_one (U : 𝒞) (x : p.Fiber U) : Θ U x 1 = 𝟙 x := by
  have h := hΘmul U x 1 ((Θ U x).symm (𝟙 x))
  rw [one_mul, Equiv.apply_symm_apply, Category.comp_id] at h
  exact h.symm

/-- Restricting a section of `𝒢` along `g` and then along `k` is restricting it along `k ≫ g`. -/
theorem map_comp_apply_eq {U V Z : 𝒞} (g : V ⟶ U) (k : Z ⟶ V) (b : 𝒢.obj.obj (op U)) :
    (𝒢.obj.map k.op) ((𝒢.obj.map g.op) b) = (𝒢.obj.map (k ≫ g).op) b :=
  map_comp_apply_eq' g k b

/-- Restricting a section of `R` along `g` and then along `k` is restricting it along `k ≫ g`. -/
theorem ring_map_comp_apply_eq {U V Z : 𝒞} (g : V ⟶ U) (k : Z ⟶ V) (r : R.obj (op U)) :
    (R.map k.op) ((R.map g.op) r) = (R.map (k ≫ g).op) r := by
  rw [op_comp, Functor.map_comp]
  rfl

include hΘmul hΘconj hΘres hcomp hid hadd hzero hone hmul hconj hpull hsh hne hlc in
/-- The module structures of the automorphism groups descend to the band: there is a
multiplication `R(U) × 𝒢(U) ⟶ 𝒢(U)`, read by every frame `y` over every `g : V ⟶ U` as the given
multiplication on `Aut(y)`, which is a module structure (the group law of `𝒢` being the addition)
and is compatible with the restriction maps. -/
theorem exists_bandSmul :
    ∃ bsmul : ∀ U : 𝒞, R.obj (op U) → 𝒢.obj.obj (op U) → 𝒢.obj.obj (op U),
      (∀ (U V : 𝒞) (g : V ⟶ U) (y : p.Fiber V) (r : R.obj (op U)) (a : 𝒢.obj.obj (op U)),
        Θ V y (𝒢.obj.map g.op (bsmul U r a)) = smul V y (R.map g.op r) (Θ V y (𝒢.obj.map g.op a))) ∧
      (∀ (U : 𝒞) (r : R.obj (op U)) (a b : 𝒢.obj.obj (op U)),
        bsmul U r (a * b) = bsmul U r a * bsmul U r b) ∧
      (∀ (U : 𝒞) (r : R.obj (op U)), bsmul U r 1 = 1) ∧
      (∀ (U : 𝒞) (r s : R.obj (op U)) (a : 𝒢.obj.obj (op U)),
        bsmul U (r + s) a = bsmul U r a * bsmul U s a) ∧
      (∀ (U : 𝒞) (a : 𝒢.obj.obj (op U)), bsmul U 0 a = 1) ∧
      (∀ (U : 𝒞) (a : 𝒢.obj.obj (op U)), bsmul U 1 a = a) ∧
      (∀ (U : 𝒞) (r s : R.obj (op U)) (a : 𝒢.obj.obj (op U)),
        bsmul U (r * s) a = bsmul U r (bsmul U s a)) ∧
      (∀ (U V : 𝒞) (h : V ⟶ U) (r : R.obj (op U)) (a : 𝒢.obj.obj (op U)),
        𝒢.obj.map h.op (bsmul U r a) = bsmul V (R.map h.op r) (𝒢.obj.map h.op a)) := by
  choose bsmul hb using fun (U : 𝒞) (r : R.obj (op U)) (a : 𝒢.obj.obj (op U)) =>
    exists_bandSmul_spec hΘconj hΘres hconj hpull hsh hne hlc r a
  have spec : ∀ (U V : 𝒞) (g : V ⟶ U) (y : p.Fiber V) (r : R.obj (op U))
      (a : 𝒢.obj.obj (op U)),
      Θ V y (𝒢.obj.map g.op (bsmul U r a)) = smul V y (R.map g.op r) (Θ V y (𝒢.obj.map g.op a)) :=
    fun U V g y r a => by rw [hb U r a V g y, Θ_bandSmulAt]
  have ext : ∀ {U : 𝒞} {b b' : 𝒢.obj.obj (op U)},
      (∀ (V : 𝒞) (g : V ⟶ U) (y : p.Fiber V),
        Θ V y (𝒢.obj.map g.op b) = Θ V y (𝒢.obj.map g.op b')) → b = b' :=
    fun h => eq_of_forall_Θ_eq hsh hne h
  refine ⟨bsmul, spec, fun U r a b => ext fun V g y => ?_, fun U r => ext fun V g y => ?_,
    fun U r s a => ext fun V g y => ?_, fun U a => ext fun V g y => ?_,
    fun U a => ext fun V g y => ?_, fun U r s a => ext fun V g y => ?_,
    fun U V h r a => ext fun Z k y => ?_⟩
  · rw [spec, map_mul (ConcreteCategory.hom (𝒢.obj.map g.op)) a b, hΘmul,
      map_mul (ConcreteCategory.hom (𝒢.obj.map g.op)) (bsmul U r a) (bsmul U r b), hΘmul, spec,
      spec, hcomp]
  · rw [spec, map_one (ConcreteCategory.hom (𝒢.obj.map g.op)), Θ_one hΘmul, hid]
  · rw [spec, map_add (ConcreteCategory.hom (R.map g.op)) r s, hadd,
      map_mul (ConcreteCategory.hom (𝒢.obj.map g.op)), hΘmul, spec, spec]
  · rw [spec, map_zero (ConcreteCategory.hom (R.map g.op)), hzero,
      map_one (ConcreteCategory.hom (𝒢.obj.map g.op)), Θ_one hΘmul]
  · rw [spec, map_one (ConcreteCategory.hom (R.map g.op)), hone]
  · rw [spec, map_mul (ConcreteCategory.hom (R.map g.op)), hmul, spec, spec]
  · rw [map_comp_apply_eq, spec, spec, map_comp_apply_eq, ring_map_comp_apply_eq]

end Module

end CategoryTheory.Functor
