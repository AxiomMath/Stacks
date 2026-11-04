module

public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.Sites.Limits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforward
import StacksCore.Tactic.StacksAttribute

/-!
# Modules over a split square-zero extension of sheaves of rings

Let `q : S ⟶ R` be a surjection of sheaves of rings whose kernel `ℐ` has square zero, and
suppose a splitting of `q` has been chosen. Writing a section `r` of `S` as `σ(q r) + d r`
with `d r` a section of `ℐ` exhibits `d` as a derivation: it kills `0` and `1`, is additive,
and satisfies the Leibniz rule `d(rs) = q r · d s + q s · d r` for the `R`-module structure
the splitting puts on `ℐ`.

Given such a `d`, two `R`-modules `ℱ` and `𝒦`, and an `R`-bilinear map `c : ℐ × ℱ ⟶ 𝒦`, the
direct sum `ℱ ⊕ 𝒦` carries an `S`-module structure

    r · (m, n) = (q r · m, q r · n + c (d r) m).

This is constructed sectionwise, for presheaves of modules, and for sheaves of modules on a site.

## Main definitions

* `Stacks.SheafOfModules.SplitSquareZero.extensionSmul` and
  `Stacks.SheafOfModules.SplitSquareZero.extensionModule`: the displayed action of a ring `S`
  on a product of two modules over a quotient `R` of it, and the module structure it defines.
* `Stacks.SheafOfModules.SplitSquareZero.extensionPresheafModule` and
  `Stacks.SheafOfModules.SplitSquareZero.extensionSheafModule`: the same for presheaves and
  sheaves of modules on a site.
* `Stacks.SheafOfModules.SplitSquareZero.productPresheaf`: the pointwise product of the
  underlying abelian presheaves of two presheaves of modules.

## Main results

* `Stacks.SheafOfModules.SplitSquareZero.isSheaf_productPresheaf`: the pointwise product of
  two sheaves of modules is a sheaf of abelian groups.

## References

* [Stacks Project, Tag 08LB](https://stacks.math.columbia.edu/tag/08LB)
* [Stacks Project, Tag 08LA](https://stacks.math.columbia.edu/tag/08LA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v₁ u₁ w

namespace Stacks.SheafOfModules.SplitSquareZero

section Product

variable {C : Type u₁} [Category.{v₁} C]

/-- The pointwise product of the underlying abelian presheaves of two presheaves of modules. -/
noncomputable def productPresheaf {R : Cᵒᵖ ⥤ RingCat.{w}} (F K : PresheafOfModules.{w} R) :
    Cᵒᵖ ⥤ Ab.{w} :=
  { obj := fun U => AddCommGrpCat.of (F.obj U × K.obj U)
    map := fun f => AddCommGrpCat.ofHom {
      toFun := fun z => (F.map f z.1, K.map f z.2)
      map_zero' := by apply Prod.ext <;> simp <;> rfl
      map_add' := by intros; apply Prod.ext <;> simp <;> rfl }
    map_id := by
      intro U
      apply AddCommGrpCat.hom_ext
      ext z <;> simp
    map_comp := by
      intro U V W f g
      apply AddCommGrpCat.hom_ext
      ext z <;> simp <;> rfl }

/-- The pointwise product of two sheaves of modules is a sheaf of abelian groups. -/
theorem isSheaf_productPresheaf {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
    (F K : SheafOfModules.{w} R) :
    Presheaf.IsSheaf J (productPresheaf F.val K.val) := by
  let fst : productPresheaf F.val K.val ⟶ F.val.presheaf :=
    { app := fun U => AddCommGrpCat.ofHom (AddMonoidHom.fst _ _)
      naturality := fun _ _ _ => rfl }
  let snd : productPresheaf F.val K.val ⟶ K.val.presheaf :=
    { app := fun U => AddCommGrpCat.ofHom (AddMonoidHom.snd _ _)
      naturality := fun _ _ _ => rfl }
  have hc : IsLimit (BinaryFan.mk fst snd) := by
    refine BinaryFan.IsLimit.mk _
      (fun {T} a b => {
        app := fun U => AddCommGrpCat.ofHom ((a.app U).hom.prod (b.app U).hom)
        naturality := fun U V f => by
          ext x
          exact Prod.ext (NatTrans.naturality_apply a f x)
            (NatTrans.naturality_apply b f x) })
      (fun a b => rfl) (fun a b => rfl) ?_
    intro T a b m ha hb
    ext U x
    exact Prod.ext (congrArg (fun g : T ⟶ F.val.presheaf => g.app U x) ha)
      (congrArg (fun g : T ⟶ K.val.presheaf => g.app U x) hb)
  exact ObjectProperty.prop_of_isLimit_binaryFan (Presheaf.IsSheaf J) hc F.isSheaf K.isSheaf

end Product

section Sections

variable {R S I F K : Type w} [Ring R] [Ring S]
  [AddCommGroup I] [AddCommGroup F] [AddCommGroup K]
  [Module R I] [Module R F] [Module R K]

/-- The action of a ring `S` on the product of two modules over a quotient ring `R` attached
to a derivation `d : S → I` and a bilinear map `c`: the quotient acts diagonally, and the
derivation part of a scalar moves the first coordinate into the second through `c`. -/
def extensionSmul (q : S →+* R) (d : S → I) (c : I → F → K) (r : S) (z : F × K) : F × K :=
  (q r • z.1, q r • z.2 + c (d r) z.1)

/-- The `S`-module structure on `F × K` determined by a derivation `d : S → I` into a module
over the quotient `R` and a bilinear map `c : I → F → K`, with scalar action `extensionSmul`. -/
@[instance_reducible]
noncomputable def extensionModule (q : S →+* R) (d : S → I) (c : I → F → K)
    (hd_zero : d 0 = 0) (hd_one : d 1 = 0)
    (hd_add : ∀ r s, d (r + s) = d r + d s)
    (hd_mul : ∀ r s, d (r * s) = q r • d s + q s • d r)
    (hc_add_left : ∀ a b m, c (a + b) m = c a m + c b m)
    (hc_add_right : ∀ a m n, c a (m + n) = c a m + c a n)
    (hc_smul_left : ∀ (r : R) a m, c (r • a) m = r • c a m)
    (hc_smul_right : ∀ (r : R) a m, c a (r • m) = r • c a m) :
    Module S (F × K) := by
  have hc_zero_left : ∀ m, c 0 m = (0 : K) := fun m => by simpa using hc_add_left 0 0 m
  have hc_zero_right : ∀ a, c a 0 = (0 : K) := fun a => by simpa using hc_add_right a 0 0
  letI : SMul S (F × K) := ⟨extensionSmul q d c⟩
  refine
    { toDistribMulAction :=
        { toMulAction := { mul_smul := ?_, one_smul := ?_ }
          smul_zero := ?_
          smul_add := ?_ }
      add_smul := ?_
      zero_smul := ?_ }
  · intro r s z
    change extensionSmul q d c (r * s) z = extensionSmul q d c r (extensionSmul q d c s z)
    apply Prod.ext
    · simp only [extensionSmul, map_mul, mul_smul]
    · change q (r * s) • z.2 + c (d (r * s)) z.1 =
        q r • (q s • z.2 + c (d s) z.1) + c (d r) (q s • z.1)
      rw [map_mul, mul_smul, hd_mul, hc_add_left, hc_smul_left, hc_smul_left, smul_add,
        hc_smul_right]
      abel
  · intro z
    change extensionSmul q d c 1 z = z
    simp [extensionSmul, hd_one, hc_zero_left]
  · intro r
    change extensionSmul q d c r 0 = 0
    simp [extensionSmul, hc_zero_right]
  · intro r x y
    change extensionSmul q d c r (x + y) =
      extensionSmul q d c r x + extensionSmul q d c r y
    change (q r • (x.1 + y.1), q r • (x.2 + y.2) + c (d r) (x.1 + y.1)) =
      (q r • x.1 + q r • y.1, (q r • x.2 + c (d r) x.1) + (q r • y.2 + c (d r) y.1))
    rw [smul_add, smul_add, hc_add_right]
    exact Prod.ext rfl (add_add_add_comm _ _ _ _)
  · intro r s z
    change extensionSmul q d c (r + s) z =
      extensionSmul q d c r z + extensionSmul q d c s z
    apply Prod.ext
    · change (q (r + s)) • z.1 = q r • z.1 + q s • z.1
      rw [map_add, add_smul]
    · change (q (r + s)) • z.2 + c (d (r + s)) z.1 =
        (q r • z.2 + c (d r) z.1) + (q s • z.2 + c (d s) z.1)
      rw [map_add, hd_add, add_smul, hc_add_left]
      abel
  · intro z
    change extensionSmul q d c 0 z = 0
    simp [extensionSmul, hd_zero, hc_zero_left]

end Sections

section Presheaf

variable {C : Type u₁} [Category.{v₁} C]

/-- The presheaf of `S`-modules on `ℱ × 𝒦` assembled from the sectionwise structures
`Stacks.SheafOfModules.SplitSquareZero.extensionModule`. The hypotheses are those of the
sectionwise construction on every open set, together with compatibility of `d` and of `c`
with restriction. -/
noncomputable def extensionPresheafModule {R S : Cᵒᵖ ⥤ RingCat.{w}}
    (I F K : PresheafOfModules.{w} R) (q : S ⟶ R)
    (d : ∀ U, S.obj U → I.obj U) (c : ∀ U, I.obj U → F.obj U → K.obj U)
    (hd_zero : ∀ U, d U 0 = 0) (hd_one : ∀ U, d U 1 = 0)
    (hd_add : ∀ U (r s : S.obj U), d U (r + s) = d U r + d U s)
    (hd_mul : ∀ U (r s : S.obj U),
      d U (r * s) = (q.app U).hom r • d U s + (q.app U).hom s • d U r)
    (hc_add_left : ∀ U (a b : I.obj U) (m : F.obj U),
      c U (a + b) m = c U a m + c U b m)
    (hc_add_right : ∀ U (a : I.obj U) (m n : F.obj U),
      c U a (m + n) = c U a m + c U a n)
    (hc_smul_left : ∀ U (r : R.obj U) (a : I.obj U) (m : F.obj U),
      c U (r • a) m = r • c U a m)
    (hc_smul_right : ∀ U (r : R.obj U) (a : I.obj U) (m : F.obj U),
      c U a (r • m) = r • c U a m)
    (d_natural : ∀ ⦃U V : Cᵒᵖ⦄ (f : U ⟶ V) (r : S.obj U),
      I.map f (d U r) = d V ((S.map f).hom r))
    (c_natural : ∀ ⦃U V : Cᵒᵖ⦄ (f : U ⟶ V) (a : I.obj U) (m : F.obj U),
      K.map f (c U a m) = c V (I.map f a) (F.map f m)) :
    PresheafOfModules.{w} S := by
  letI (U : Cᵒᵖ) : Module (S.obj U) ((productPresheaf F K).obj U) := by
    change Module (S.obj U) (F.obj U × K.obj U)
    exact extensionModule (q.app U).hom (d U) (c U) (hd_zero U) (hd_one U) (hd_add U)
      (hd_mul U) (hc_add_left U) (hc_add_right U) (hc_smul_left U) (hc_smul_right U)
  refine @PresheafOfModules.ofPresheaf _ _ S (productPresheaf F K) (fun U => this U) ?_
  intro U V f r z
  have hq : (R.map f).hom ((q.app U).hom r) = (q.app V).hom ((S.map f).hom r) :=
    congrArg (fun h : S.obj U ⟶ R.obj V => h.hom r) (q.naturality f).symm
  apply Prod.ext
  · change F.map f ((q.app U).hom r • z.1) = (q.app V).hom ((S.map f).hom r) • F.map f z.1
    rw [F.map_smul, hq]
  · change K.map f ((q.app U).hom r • z.2 + c U (d U r) z.1) =
      (q.app V).hom ((S.map f).hom r) • (show K.obj V from K.map f z.2) +
        c V (d V ((S.map f).hom r)) (F.map f z.1)
    rw [map_add, K.map_smul, c_natural f (d U r) z.1, d_natural f r]
    change (R.map f).hom ((q.app U).hom r) • (show K.obj V from K.map f z.2) +
        c V (d V ((S.map f).hom r)) (F.map f z.1) = _
    rw [hq]

end Presheaf

section Sheaf

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}

/-- The sheaf of `S`-modules `ℱ ⊕ 𝒦` determined by a derivation `d` into `ℐ` and a bilinear
map `c : ℐ → ℱ → 𝒦`, whose underlying presheaf of modules is
`Stacks.SheafOfModules.SplitSquareZero.extensionPresheafModule`. -/
noncomputable def extensionSheafModule {R S : Sheaf J RingCat.{w}} (q : S ⟶ R)
    (I F K : SheafOfModules.{w} R)
    (d : ∀ U, S.obj.obj U → I.val.obj U) (c : ∀ U, I.val.obj U → F.val.obj U → K.val.obj U)
    (hd_zero : ∀ U, d U 0 = 0) (hd_one : ∀ U, d U 1 = 0)
    (hd_add : ∀ U (r s : S.obj.obj U), d U (r + s) = d U r + d U s)
    (hd_mul : ∀ U (r s : S.obj.obj U),
      d U (r * s) = (q.hom.app U).hom r • d U s + (q.hom.app U).hom s • d U r)
    (hc_add_left : ∀ U (a b : I.val.obj U) (m : F.val.obj U),
      c U (a + b) m = c U a m + c U b m)
    (hc_add_right : ∀ U (a : I.val.obj U) (m n : F.val.obj U),
      c U a (m + n) = c U a m + c U a n)
    (hc_smul_left : ∀ U (r : R.obj.obj U) (a : I.val.obj U) (m : F.val.obj U),
      c U (r • a) m = r • c U a m)
    (hc_smul_right : ∀ U (r : R.obj.obj U) (a : I.val.obj U) (m : F.val.obj U),
      c U a (r • m) = r • c U a m)
    (d_natural : ∀ ⦃U V : Cᵒᵖ⦄ (f : U ⟶ V) (r : S.obj.obj U),
      I.val.map f (d U r) = d V ((S.obj.map f).hom r))
    (c_natural : ∀ ⦃U V : Cᵒᵖ⦄ (f : U ⟶ V) (a : I.val.obj U) (m : F.val.obj U),
      K.val.map f (c U a m) = c V (I.val.map f a) (F.val.map f m)) :
    SheafOfModules.{w} S :=
  ⟨extensionPresheafModule I.val F.val K.val q.hom d c hd_zero hd_one hd_add hd_mul
    hc_add_left hc_add_right hc_smul_left hc_smul_right d_natural c_natural,
    isSheaf_productPresheaf F K⟩

end Sheaf

end Stacks.SheafOfModules.SplitSquareZero

end
