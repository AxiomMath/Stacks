module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.LocalSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DiagonalMorphism
import StacksCore.Tactic.StacksAttribute

/-! # The currying isomorphism of internal Hom complexes on a ringed site

Let `(C, O)` be a ringed site and let `K`, `L` and `M` be complexes of `O`-modules. **Stacks
0A90** identifies

`SheafHom(K, SheafHom(L, M))` with `SheafHom(Tot(K ⊗_O L), M)`,

and this file constructs that isomorphism of complexes of `O`-modules. On local sections over an
object `U` of the site it is the transposition
`AlgebraicGeometry.RingedSite.curryCochain` of
`StacksDraft.Ch21.Sec34.CurryingOnASlice`: a degree-`n` section `α` of
`SheafHom(K, SheafHom(L, M))` over `U` goes to the degree-`n` cochain out of
`Tot(K ⊗_O L)|_U` whose value on the restricted pure tensor of a section `k` of `K^t` and a
section `l` of `L^r` is `α(k)(l)`, with no sign.

The construction has three steps. First, currying commutes with the two Hom-complex
differentials: this is where the Koszul signs of the total tensor complex
(`AlgebraicGeometry.RingedSite.tensorComplexOverSection_d`) meet those of the Hom-complex
differential (`AlgebraicGeometry.RingedSite.applyHomSectionOver_differential`), and the sign
identity that makes them cancel is `(-1)^(t + n + 1) = (-1)^(n + 1) (-1)^t`. Second, the inverse
is built elementwise: a cochain `β` out of `Tot(K ⊗_O L)|_U` is sent to the cochain taking a
section `k` of `K^t` to the section of `SheafHom(L, M)` whose cochain is `l ↦ β(k ⊗ l)`. Third,
the two are mutually inverse — one way because a section of the internal Hom complex is
determined by its values (`AlgebraicGeometry.RingedSite.homSection_ext`), the other because a
morphism out of the restricted total tensor complex is determined by its values on the restricted
pure tensors (`AlgebraicGeometry.RingedSite.tensorComplexOverSection_hom_ext`).

Naturality of the isomorphism in the three complexes is
`StacksDraft.Ch21.Sec34.CurryingIsoNaturality`.

## Main definitions

* `AlgebraicGeometry.RingedSite.curryFun` and `AlgebraicGeometry.RingedSite.uncurryFun`:
  currying and uncurrying of local sections.
* `AlgebraicGeometry.RingedSite.uncurryValue`, `uncurryInnerHom`, `uncurryInnerCochain`,
  `uncurrySection`, `uncurryComponent`, `uncurryCochain`: the elementwise construction of the
  uncurried cochain.
* `AlgebraicGeometry.RingedSite.curryHom`, `AlgebraicGeometry.RingedSite.uncurryHom` and
  `AlgebraicGeometry.RingedSite.curryIsoX`: the degreewise morphisms and isomorphism.
* `AlgebraicGeometry.RingedSite.sheafHomTensorCurryIso`: the currying isomorphism of complexes.

## Main results

* `AlgebraicGeometry.RingedSite.curryCochain_delta`: currying commutes with the Hom-complex
  differentials.
* `AlgebraicGeometry.RingedSite.homSection_tensor_ext`: a local section of
  `SheafHom(Tot(K ⊗_O L), M)` is determined by its values on the local pure tensors.
* `AlgebraicGeometry.RingedSite.uncurryFun_curryFun` and
  `AlgebraicGeometry.RingedSite.curryFun_uncurryFun`: currying and uncurrying are mutually
  inverse.
* `AlgebraicGeometry.RingedSite.applyHomSectionOver_curryFun`: the curried section evaluates on
  a local pure tensor by `AlgebraicGeometry.RingedSite.curryRule`, which pins the isomorphism
  down.

## Implementation notes

Two spellings of one module structure meet throughout, and the whole file is arranged so that
each statement sits at one of them. A section of a restricted complex `A|_U` over an object
`Over.mk g` of the slice site is a section of `A` over the source of `g`, but its scalars are
spelled `(O|_U)(Over.mk g)` in the first case and `O(W)` in the second; the two are
definitionally equal and only the first is found by instance search. Accordingly: the arguments
and values of `uncurryValue` and of `cochainOutValue` are declared at the *ambient* spelling, so
that `map_add`/`map_smul` and the bilinearity of
`AlgebraicGeometry.RingedSite.tensorComplexSection` apply to them directly; and the morphisms of
sheaves of `O|_U`-modules are assembled with `PresheafOfModules.homMk`, which asks for a
morphism of presheaves of abelian groups together with a linearity condition, rather than with
`ModuleCat.ofHom`, whose `Module` instance over the restricted sheaf of rings is not found.
Restriction of a section is always written `AlgebraicGeometry.RingedSite.restrictSection`, whose
declared type is the ambient one, for the same reason: `(A.val.map g.op x)` has the type of a
restriction of scalars, and a goal containing it is not type-correct at the `implicit`
transparency level, after which every rewrite fails.

The sign bookkeeping of `curryCochain_delta` is isolated in a lemma over an abstract abelian
group, since `smul_add` does not fire at the mixed spelling the goal reaches.

The properties of `uncurryFun` are deduced from those of `curryFun` through the bijection rather
than proved directly, which halves the elementwise work.

The degreewise morphisms, in contrast, are morphisms of sheaves of `O`-modules on the ambient
site, so they are assembled directly from their action on sections; and the isomorphism of
complexes is `HomologicalComplex.Hom.isoOfComponents`, which asks for the compatibility with the
differentials in one direction only.

## References

* [Stacks Project, Tag 0A90](https://stacks.math.columbia.edu/tag/0A90)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite CochainComplex.HomComplex

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  ringSheafOverSectionsCommRing

/-- The sign bookkeeping of the two Leibniz rules, over an abstract abelian group. -/
private lemma negOnePow_leibniz_algebra {A : Type*} [AddCommGroup A] (t n : ℤ) (D c₂ c₃ : A) :
    D + ((n + 1).negOnePow : ℤ) • (c₂ + (t.negOnePow : ℤ) • c₃) =
      D + (t + n + 1).negOnePow • c₃ + (n + 1).negOnePow • c₂ := by
  have h : ((t + n + 1).negOnePow : ℤ) = ((n + 1).negOnePow : ℤ) * (t.negOnePow : ℤ) := by
    rw [show t + n + 1 = n + 1 + t by ring, Int.negOnePow_add, Units.val_mul]
  simp only [Units.smul_def, smul_add, smul_smul, h]
  abel

variable (X : RingedSite.{u, u, u})

/-- Evaluation is `ℤˣ`-linear in the Hom section, for a source section over the same object. -/
lemma applyHomSection_units_zsmul_left
    {K' L' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (H : SheafHomComplex X K' L')
    (U : X.C) (n p q : ℤ) (hpq : p + n = q) (c : ℤˣ) (f : (H.obj.X n).val.obj (op U))
    (x : (K'.X p).val.obj (op U)) :
    applyHomSection X H U n p q hpq (c • f) x =
      c • applyHomSection X H U n p q hpq f x :=
  applyHomSectionOver_units_zsmul_left X H U U (𝟙 U) n p q hpq c f x

variable (U : X.C)

/-- The Hom-complex differential of a cochain between restricted complexes, on sections, with
the intermediate degree named. -/
private lemma delta_val_app_apply
    {A B : CochainComplex
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) ℤ}
    (n m : ℤ) (hnm : n + 1 = m) (z : Cochain A B n) (p q a : ℤ) (hpq : p + m = q)
    (ha : a = q - 1) (V : (Over U)ᵒᵖ) (x : (A.X p).val.obj V) :
    ((δ n m z).v p q hpq).val.app V x =
      (B.d a q).val.app V ((z.v p a (by omega)).val.app V x) +
        m.negOnePow • ((z.v (p + 1) q (by omega)).val.app V
          ((A.d p (p + 1)).val.app V x)) := by
  rw [δ_v n m hnm z p q hpq a (p + 1) ha rfl]
  simp only [add_val_app_apply, units_zsmul_val_app_apply, comp_val_app_apply]

/-- The differential of a restricted complex acts on sections by the original differential. -/
private lemma restrictComplex_d_val_app
    (A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (p q : ℤ) {W : X.C} (g : W ⟶ U)
    (x : (A.X p).val.obj (op W)) :
    ((restrictComplex X A U).d p q).val.app (op (Over.mk g)) x =
      (A.d p q).val.app (op W) x := rfl

variable
  {K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
  {n : ℤ}
variable (α : ((sheafHomComplex X K (sheafHomComplex X L M).obj).obj.X n).val.obj (op U))

/-! ## Elementary properties of the currying rule -/

/-- `AlgebraicGeometry.RingedSite.curryRule` with the intermediate degree named. -/
lemma curryRule_degree (t r d q : ℤ) (htq : t + n = q) (hd : r + q = d) {W : X.C}
    (g : W ⟶ U) (k : (K.X t).val.obj (op W)) (l : (L.X r).val.obj (op W)) :
    applyHomSection X (sheafHomComplex X L M) W q r d hd
        (applyHomSectionOver X (sheafHomComplex X K (sheafHomComplex X L M).obj) U W g n t q
          htq α k) l =
      curryRule X U K L M n α t r d (by omega) g k l := by
  subst htq
  rfl

/-- `AlgebraicGeometry.RingedSite.curryRule` is additive in the Hom section. -/
lemma curryRule_add_section (t r d : ℤ) (hd : r + (t + n) = d) {W : X.C} (g : W ⟶ U)
    (α' : ((sheafHomComplex X K (sheafHomComplex X L M).obj).obj.X n).val.obj (op U))
    (k : (K.X t).val.obj (op W)) (l : (L.X r).val.obj (op W)) :
    curryRule X U K L M n (α + α') t r d hd g k l =
      curryRule X U K L M n α t r d hd g k l + curryRule X U K L M n α' t r d hd g k l := by
  rw [curryRule, applyHomSectionOver_add_left, applyHomSection_add_left]

/-- `AlgebraicGeometry.RingedSite.curryRule` is semilinear in the Hom section. -/
lemma curryRule_smul_section (t r d : ℤ) (hd : r + (t + n) = d) {W : X.C} (g : W ⟶ U)
    (s : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)) (k : (K.X t).val.obj (op W))
    (l : (L.X r).val.obj (op W)) :
    curryRule X U K L M n (s • α) t r d hd g k l =
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map g.op s •
        curryRule X U K L M n α t r d hd g k l := by
  rw [← curryRule_degree X U (s • α) t r d (t + n) rfl hd g k l,
    ← curryRule_degree X U α t r d (t + n) rfl hd g k l,
    applyHomSectionOver_smul_left, applyHomSection_smul_left]

/-- `AlgebraicGeometry.RingedSite.curryRule` for a restricted Hom section. -/
lemma curryRule_restrict_section {V : X.C} (i : V ⟶ U) (t r d : ℤ) (hd : r + (t + n) = d)
    {W : X.C} (g : W ⟶ V) (k : (K.X t).val.obj (op W)) (l : (L.X r).val.obj (op W)) :
    curryRule X V K L M n (restrictSection X i α) t r d hd g k l =
      curryRule X U K L M n α t r d hd (g ≫ i) k l := by
  rw [← curryRule_degree X V (restrictSection X i α) t r d (t + n) rfl hd g k l,
    ← curryRule_degree X U α t r d (t + n) rfl hd (g ≫ i) k l,
    ← applyHomSectionOver_restrict_comp]

variable [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctorReg K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-! ## Currying commutes with the differentials -/

/-- **Currying commutes with the Hom-complex differentials.** The curried cochain of the
differential of a local section `α` of `SheafHom(K, SheafHom(L, M))` is the Hom-complex
differential of the curried cochain of `α`. -/
lemma curryCochain_delta :
    δ n (n + 1) (curryCochain α) =
      curryCochain (((sheafHomComplex X K (sheafHomComplex X L M).obj).obj.d n (n + 1)).val.app
        (op U) α) := by
  refine Cochain.ext _ _ fun c p hcp ↦ ?_
  refine tensorComplexOverSection_hom_ext fun t r htr W g k l ↦ ?_
  rw [delta_val_app_apply X U n (n + 1) rfl (curryCochain α) c p (p - 1) hcp rfl,
    curryCochain_v_section α c (p - 1) (by omega) t r htr g k l,
    tensorComplexOverSection_d X U t r c (c + 1) htr rfl g k l]
  simp only [Units.smul_def, map_add, map_zsmul]
  rw [curryCochain_v_section α (c + 1) p (by omega) (t + 1) r (by omega) g _ l,
    curryCochain_v_section α (c + 1) p (by omega) t (r + 1) (by omega) g k _,
    curryCochain_v_section _ c p hcp t r htr g k l]
  rw [← curryRule_degree X U
      (((sheafHomComplex X K (sheafHomComplex X L M).obj).obj.d n (n + 1)).val.app (op U) α)
      t r p (t + n + 1) (by omega) (by omega) g k l,
    applyHomSectionOver_differential X (sheafHomComplex X K (sheafHomComplex X L M).obj) U W g
      n t (t + n) (t + n + 1) rfl rfl α k,
    applyHomSection_add_left, applyHomSection_units_zsmul_left,
    applyHomSection_differential X (sheafHomComplex X L M) W (t + n) r (p - 1) p
      (by omega) (by omega)
      (applyHomSectionOver X (sheafHomComplex X K (sheafHomComplex X L M).obj) U W g n t (t + n)
        rfl α k) l,
    curryRule_degree X U α t r (p - 1) (t + n) rfl (by omega) g k l,
    curryRule_degree X U α t (r + 1) p (t + n) rfl (by omega) g k _,
    curryRule_degree X U α (t + 1) r p (t + n + 1) (by omega) (by omega) g _ l,
    ← restrictComplex_d_val_app X U M (p - 1) p g (curryRule X U K L M n α t r (p - 1)
      (by omega) g k l)]
  exact negOnePow_leibniz_algebra t n _ _ _

/-! ## Uncurrying -/

variable (β : Cochain (restrictComplex X (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj
  K).obj L) U)
  (restrictComplex X M U) n)

/-- The value of a cochain out of the restricted total tensor complex on a local section of the
total tensor complex, with the types of the argument and the value spelled on the ambient
site. -/
abbrev cochainOutValue (c d : ℤ) (hcd : c + n = d) {W V : X.C} (g : W ⟶ U) (i : V ⟶ W)
    (y : ((((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K).obj L).X c).val.obj (op V)) :
    (M.X d).val.obj (op V) :=
  (β.v c d hcd).val.app (op (Over.mk (i ≫ g))) y

/-- `cochainOutValue` is additive. -/
lemma cochainOutValue_add (c d : ℤ) (hcd : c + n = d) {W V : X.C} (g : W ⟶ U) (i : V ⟶ W)
    (y y' : ((((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K).obj L).X c).val.obj (op V)) :
    cochainOutValue X U β c d hcd g i (y + y') =
      cochainOutValue X U β c d hcd g i y + cochainOutValue X U β c d hcd g i y' :=
  map_add _ y y'

/-- `cochainOutValue` is linear. -/
lemma cochainOutValue_smul (c d : ℤ) (hcd : c + n = d) {W V : X.C} (g : W ⟶ U) (i : V ⟶ W)
    (s : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V))
    (y : ((((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K).obj L).X c).val.obj (op V)) :
    cochainOutValue X U β c d hcd g i (s • y) = s • cochainOutValue X U β c d hcd g i y :=
  map_smul _ s y

/-- `cochainOutValue` is compatible with restriction. -/
lemma cochainOutValue_restrict (c d : ℤ) (hcd : c + n = d) {W V V' : X.C} (g : W ⟶ U)
    (i : V ⟶ W) (j : V' ⟶ V)
    (y : ((((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K).obj L).X c).val.obj (op V)) :
    cochainOutValue X U β c d hcd g (j ≫ i) (restrictSection X j y) =
      restrictSection X j (cochainOutValue X U β c d hcd g i y) :=
  PresheafOfModules.naturality_apply (β.v c d hcd).val
    (Over.homMk j (by simp) : Over.mk ((j ≫ i) ≫ g) ⟶ Over.mk (i ≫ g)).op y

/-- The value of the uncurried cochain of `β`: the value of `β` on the local pure tensor of the
restriction of a fixed section `k` of `K^t` and a section `l` of `L^r`. -/
def uncurryValue (t : ℤ) {W : X.C} (g : W ⟶ U) (k : (K.X t).val.obj (op W))
    (r d : ℤ) (hd : t + r + n = d) {V : X.C} (i : V ⟶ W) (l : (L.X r).val.obj (op V)) :
    (M.X d).val.obj (op V) :=
  cochainOutValue X U β (t + r) d hd g i
    (tensorComplexSection X (K := K) (L := L) (W := V) t r (t + r) rfl
      (restrictSection X i k) l)

/-- `uncurryValue` is additive in the section of `L`. -/
lemma uncurryValue_add_right (t : ℤ) {W : X.C} (g : W ⟶ U) (k : (K.X t).val.obj (op W))
    (r d : ℤ) (hd : t + r + n = d) {V : X.C} (i : V ⟶ W) (l l' : (L.X r).val.obj (op V)) :
    uncurryValue X U β t g k r d hd i (l + l') =
      uncurryValue X U β t g k r d hd i l + uncurryValue X U β t g k r d hd i l' := by
  rw [uncurryValue, uncurryValue, uncurryValue, tensorComplexSection_add_right,
    cochainOutValue_add]

/-- `uncurryValue` is linear in the section of `L`. -/
lemma uncurryValue_smul_right (t : ℤ) {W : X.C} (g : W ⟶ U) (k : (K.X t).val.obj (op W))
    (r d : ℤ) (hd : t + r + n = d) {V : X.C} (i : V ⟶ W)
    (s : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V)) (l : (L.X r).val.obj (op V)) :
    uncurryValue X U β t g k r d hd i (s • l) = s • uncurryValue X U β t g k r d hd i l := by
  rw [uncurryValue, uncurryValue, tensorComplexSection_smul_right, cochainOutValue_smul]

/-- `uncurryValue` is additive in the section of `K`. -/
lemma uncurryValue_add_left (t : ℤ) {W : X.C} (g : W ⟶ U) (k k' : (K.X t).val.obj (op W))
    (r d : ℤ) (hd : t + r + n = d) {V : X.C} (i : V ⟶ W) (l : (L.X r).val.obj (op V)) :
    uncurryValue X U β t g (k + k') r d hd i l =
      uncurryValue X U β t g k r d hd i l + uncurryValue X U β t g k' r d hd i l := by
  rw [uncurryValue, uncurryValue, uncurryValue, restrictSection_add,
    tensorComplexSection_add_left, cochainOutValue_add]

/-- `uncurryValue` is semilinear in the section of `K`. -/
lemma uncurryValue_smul_left (t : ℤ) {W : X.C} (g : W ⟶ U)
    (s : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)) (k : (K.X t).val.obj (op W))
    (r d : ℤ) (hd : t + r + n = d) {V : X.C} (i : V ⟶ W) (l : (L.X r).val.obj (op V)) :
    uncurryValue X U β t g (s • k) r d hd i l =
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map i.op s •
        uncurryValue X U β t g k r d hd i l := by
  rw [uncurryValue, uncurryValue, restrictSection_smul, tensorComplexSection_smul_left,
    cochainOutValue_smul]

/-- `uncurryValue` is compatible with restriction of the section of `L` and of the arrow. -/
lemma uncurryValue_restrict (t : ℤ) {W : X.C} (g : W ⟶ U) (k : (K.X t).val.obj (op W))
    (r d : ℤ) (hd : t + r + n = d) {V V' : X.C} (i : V ⟶ W) (j : V' ⟶ V)
    (l : (L.X r).val.obj (op V)) :
    uncurryValue X U β t g k r d hd (j ≫ i) (restrictSection X j l) =
      restrictSection X j (uncurryValue X U β t g k r d hd i l) := by
  rw [uncurryValue, uncurryValue, restrictSection_comp, restrictSection,
    tensorComplexSection_restrict, ← restrictSection, cochainOutValue_restrict]

/-- `uncurryValue` is compatible with restriction of the section of `K`. -/
lemma uncurryValue_restrict_left (t : ℤ) {W W' : X.C} (g : W ⟶ U) (h : W' ⟶ W)
    (k : (K.X t).val.obj (op W)) (r d : ℤ) (hd : t + r + n = d) {V : X.C} (i : V ⟶ W')
    (l : (L.X r).val.obj (op V)) :
    uncurryValue X U β t (h ≫ g) (restrictSection X h k) r d hd i l =
      uncurryValue X U β t g k r d hd (i ≫ h) l := by
  rw [uncurryValue, uncurryValue, ← restrictSection_comp, cochainOutValue, cochainOutValue,
    Category.assoc]

/-- The map on sections underlying `uncurryInnerHom`. -/
def uncurryInnerPresheafMap (t q : ℤ) (htq : t + n = q) {W : X.C} (g : W ⟶ U)
    (k : (K.X t).val.obj (op W)) (r d : ℤ) (hrd : r + q = d) :
    ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W).obj
        (L.X r)).val.presheaf ⟶
      ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W).obj
        (M.X d)).val.presheaf where
  app Z := AddCommGrpCat.ofHom
    (AddMonoidHom.mk' (fun l ↦ uncurryValue X U β t g k r d (by omega) Z.unop.hom l)
      (fun l l' ↦ uncurryValue_add_right X U β t g k r d (by omega) Z.unop.hom l l'))
  naturality := by
    intro Z Z' f
    ext l
    have hw : Z'.unop.hom = f.unop.left ≫ Z.unop.hom := (Over.w f.unop).symm
    change uncurryValue X U β t g k r d (by omega) Z'.unop.hom
        (restrictSection X f.unop.left l) =
      restrictSection X f.unop.left (uncurryValue X U β t g k r d (by omega) Z.unop.hom l)
    rw [hw]
    exact uncurryValue_restrict X U β t g k r d (by omega) Z.unop.hom f.unop.left l

/-- The degree-`(r, d)` component of the uncurried cochain's value on `k`: a morphism of sheaves
of `O|_W`-modules from `(L^r)|_W` to `(M^d)|_W`. -/
def uncurryInnerHom (t q : ℤ) (htq : t + n = q) {W : X.C} (g : W ⟶ U)
    (k : (K.X t).val.obj (op W)) (r d : ℤ) (hrd : r + q = d) :
    (restrictComplex X L W).X r ⟶ (restrictComplex X M W).X d :=
  ⟨PresheafOfModules.homMk (uncurryInnerPresheafMap X U β t q htq g k r d hrd)
    (fun Z s l ↦ uncurryValue_smul_right X U β t g k r d (by omega) Z.unop.hom s l)⟩

/-- `uncurryInnerHom` acts on sections by `uncurryValue`. -/
lemma uncurryInnerHom_app (t q : ℤ) (htq : t + n = q) {W : X.C} (g : W ⟶ U)
    (k : (K.X t).val.obj (op W)) (r d : ℤ) (hrd : r + q = d) {V : X.C} (i : V ⟶ W)
    (l : (L.X r).val.obj (op V)) :
    (uncurryInnerHom X U β t q htq g k r d hrd).val.app (op (Over.mk i)) l =
      uncurryValue X U β t g k r d (by omega) i l := rfl

/-- The uncurried cochain's value on `k`: a degree-`q` cochain from `L|_W` to `M|_W`. -/
def uncurryInnerCochain (t q : ℤ) (htq : t + n = q) {W : X.C} (g : W ⟶ U)
    (k : (K.X t).val.obj (op W)) :
    Cochain (restrictComplex X L W) (restrictComplex X M W) q :=
  Cochain.mk fun r d hrd ↦ uncurryInnerHom X U β t q htq g k r d hrd

/-- The uncurried cochain's value on `k`, as a local section of the internal Hom complex. -/
def uncurrySection (t q : ℤ) (htq : t + n = q) {W : X.C} (g : W ⟶ U)
    (k : (K.X t).val.obj (op W)) : ((sheafHomComplex X L M).obj.X q).val.obj (op W) :=
  ((sheafHomComplex X L M).sectionsEquiv W q).symm (uncurryInnerCochain X U β t q htq g k)

/-- The defining property of `uncurrySection`. -/
lemma applyHomSectionOver_uncurrySection (t q : ℤ) (htq : t + n = q) {W : X.C} (g : W ⟶ U)
    (k : (K.X t).val.obj (op W)) (r d : ℤ) (hrd : r + q = d) {V : X.C} (i : V ⟶ W)
    (l : (L.X r).val.obj (op V)) :
    applyHomSectionOver X (sheafHomComplex X L M) W V i q r d hrd
        (uncurrySection X U β t q htq g k) l =
      uncurryValue X U β t g k r d (by omega) i l := by
  rw [applyHomSectionOver, uncurrySection,
    ((sheafHomComplex X L M).sectionsEquiv W q).apply_symm_apply, uncurryInnerCochain,
    Cochain.mk_v]
  exact uncurryInnerHom_app X U β t q htq g k r d hrd i l


/-- `uncurrySection` is additive in the section of `K`. -/
lemma uncurrySection_add (t q : ℤ) (htq : t + n = q) {W : X.C} (g : W ⟶ U)
    (k k' : (K.X t).val.obj (op W)) :
    uncurrySection X U β t q htq g (k + k') =
      uncurrySection X U β t q htq g k + uncurrySection X U β t q htq g k' := by
  refine homSection_ext X (sheafHomComplex X L M) W q fun r d hrd V i l ↦ ?_
  rw [applyHomSectionOver_uncurrySection, applyHomSectionOver_add_left,
    applyHomSectionOver_uncurrySection, applyHomSectionOver_uncurrySection,
    uncurryValue_add_left]

/-- `uncurrySection` is semilinear in the section of `K`. -/
lemma uncurrySection_smul (t q : ℤ) (htq : t + n = q) {W : X.C} (g : W ⟶ U)
    (s : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)) (k : (K.X t).val.obj (op W)) :
    uncurrySection X U β t q htq g (s • k) = s • uncurrySection X U β t q htq g k := by
  refine homSection_ext X (sheafHomComplex X L M) W q fun r d hrd V i l ↦ ?_
  rw [applyHomSectionOver_uncurrySection, applyHomSectionOver_smul_left,
    applyHomSectionOver_uncurrySection, uncurryValue_smul_left]

/-- `uncurrySection` is compatible with restriction along an arrow of the site. -/
lemma uncurrySection_restrict (t q : ℤ) (htq : t + n = q) {W W' : X.C} (g : W ⟶ U) (h : W' ⟶ W)
    (k : (K.X t).val.obj (op W)) :
    uncurrySection X U β t q htq (h ≫ g) (restrictSection X h k) =
      restrictSection X h (uncurrySection X U β t q htq g k) := by
  refine homSection_ext X (sheafHomComplex X L M) W' q fun r d hrd V i l ↦ ?_
  rw [applyHomSectionOver_uncurrySection, ← applyHomSectionOver_restrict_comp,
    applyHomSectionOver_uncurrySection, uncurryValue_restrict_left]

/-- The map on sections underlying `uncurryComponent`. -/
def uncurryComponentPresheafMap (t q : ℤ) (htq : t + n = q) :
    ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).obj
        (K.X t)).val.presheaf ⟶
      ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).obj
        ((sheafHomComplex X L M).obj.X q)).val.presheaf where
  app V := AddCommGrpCat.ofHom
    (AddMonoidHom.mk' (fun k ↦ uncurrySection X U β t q htq V.unop.hom k)
      (fun k k' ↦ uncurrySection_add X U β t q htq V.unop.hom k k'))
  naturality := by
    intro V V' f
    ext k
    have hw : V'.unop.hom = f.unop.left ≫ V.unop.hom := (Over.w f.unop).symm
    change uncurrySection X U β t q htq V'.unop.hom (restrictSection X f.unop.left k) =
      restrictSection X f.unop.left (uncurrySection X U β t q htq V.unop.hom k)
    rw [hw]
    exact uncurrySection_restrict X U β t q htq V.unop.hom f.unop.left k

/-- The degree-`(t, q)` component of the uncurried cochain of `β`. -/
def uncurryComponent (t q : ℤ) (htq : t + n = q) :
    (restrictComplex X K U).X t ⟶
      (restrictComplex X (sheafHomComplex X L M).obj U).X q :=
  ⟨PresheafOfModules.homMk (uncurryComponentPresheafMap X U β t q htq)
    (fun V s k ↦ uncurrySection_smul X U β t q htq V.unop.hom s k)⟩

/-- `uncurryComponent` acts on sections by `uncurrySection`. -/
lemma uncurryComponent_app (t q : ℤ) (htq : t + n = q) {W : X.C} (g : W ⟶ U)
    (k : (K.X t).val.obj (op W)) :
    (uncurryComponent X U β t q htq).val.app (op (Over.mk g)) k =
      uncurrySection X U β t q htq g k := rfl

/-- The uncurried cochain of `β`: the degree-`n` cochain from `K|_U` to `SheafHom(L, M)|_U`
whose value on a section `k` of `K^t` is the cochain `l ↦ β(k ⊗ l)`. -/
def uncurryCochain :
    Cochain (restrictComplex X K U) (restrictComplex X (sheafHomComplex X L M).obj U) n :=
  Cochain.mk fun t q htq ↦ uncurryComponent X U β t q htq

/-- The defining property of `uncurryCochain`. -/
lemma uncurryCochain_v (t q : ℤ) (htq : t + n = q) {W : X.C} (g : W ⟶ U)
    (k : (K.X t).val.obj (op W)) :
    ((uncurryCochain X U β).v t q htq).val.app (op (Over.mk g)) k =
      uncurrySection X U β t q htq g k := by
  rw [uncurryCochain, Cochain.mk_v]
  exact uncurryComponent_app X U β t q htq g k



/-! ## Currying and uncurrying on local sections -/

variable (φ : ((sheafHomComplex X (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K).obj L)
  M).obj.X
  n).val.obj (op U))

/-- The curried local section: the degree-`n` local section of
`SheafHom(Tot(K ⊗_O L), M)` over `U` whose cochain is the curried cochain of `α`. -/
def curryFun :
    ((sheafHomComplex X (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K).obj L) M).obj.X
      n).val.obj (op U) :=
  ((sheafHomComplex X (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K).obj L)
    M).sectionsEquiv
    U n).symm (curryCochain α)

/-- The uncurried local section: the degree-`n` local section of
`SheafHom(K, SheafHom(L, M))` over `U` whose cochain is the uncurried cochain of the cochain
of `φ`. -/
def uncurryFun : ((sheafHomComplex X K (sheafHomComplex X L M).obj).obj.X n).val.obj (op U) :=
  ((sheafHomComplex X K (sheafHomComplex X L M).obj).sectionsEquiv U n).symm
    (uncurryCochain X U
      ((sheafHomComplex X (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K).obj L)
        M).sectionsEquiv
        U n φ))

/-- The defining property of `curryFun`: it evaluates on a local pure tensor by `curryRule`. -/
lemma applyHomSectionOver_curryFun (c d : ℤ) (hcd : c + n = d) (t r : ℤ) (htr : t + r = c)
    {W : X.C} (g : W ⟶ U) (k : (K.X t).val.obj (op W)) (l : (L.X r).val.obj (op W)) :
    applyHomSectionOver X
        (sheafHomComplex X (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K).obj L) M) U W g
          n c d hcd
        (curryFun X U α) (tensorComplexSection X t r c htr k l) =
      curryRule X U K L M n α t r d (by omega) g k l := by
  rw [applyHomSectionOver, curryFun,
    ((sheafHomComplex X (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K).obj L)
      M).sectionsEquiv
      U n).apply_symm_apply, ← tensorComplexOverSection_eq X U t r c htr g k l]
  exact curryCochain_v_section α c d hcd t r htr g k l

/-- The defining property of `uncurryFun`. -/
lemma applyHomSectionOver_uncurryFun (t q : ℤ) (htq : t + n = q) {W : X.C} (g : W ⟶ U)
    (k : (K.X t).val.obj (op W)) :
    applyHomSectionOver X (sheafHomComplex X K (sheafHomComplex X L M).obj) U W g n t q htq
        (uncurryFun X U φ) k =
      uncurrySection X U
        ((sheafHomComplex X (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K).obj L)
          M).sectionsEquiv
          U n φ) t q htq g k := by
  rw [applyHomSectionOver, uncurryFun,
    ((sheafHomComplex X K (sheafHomComplex X L M).obj).sectionsEquiv U n).apply_symm_apply]
  exact uncurryCochain_v X U _ t q htq g k

/-- Evaluating the uncurried section twice gives the value of `φ` on the local pure tensor. -/
lemma applyHomSectionOver_applyHomSectionOver_uncurryFun (t q : ℤ) (htq : t + n = q) (r d : ℤ)
    (hrd : r + q = d) {W V : X.C} (g : W ⟶ U) (i : V ⟶ W) (k : (K.X t).val.obj (op W))
    (l : (L.X r).val.obj (op V)) :
    applyHomSectionOver X (sheafHomComplex X L M) W V i q r d hrd
        (applyHomSectionOver X (sheafHomComplex X K (sheafHomComplex X L M).obj) U W g n t q htq
          (uncurryFun X U φ) k) l =
      applyHomSectionOver X
        (sheafHomComplex X (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K).obj L) M) U V
          (i ≫ g) n
        (t + r) d (by omega) φ
        (tensorComplexSection X t r (t + r) rfl (restrictSection X i k) l) := by
  rw [applyHomSectionOver_uncurryFun, applyHomSectionOver_uncurrySection, uncurryValue]

/-- `curryRule` for an uncurried section is the value of `φ` on the local pure tensor. -/
lemma curryRule_uncurryFun (t r d : ℤ) (hd : r + (t + n) = d) {W : X.C} (g : W ⟶ U)
    (k : (K.X t).val.obj (op W)) (l : (L.X r).val.obj (op W)) :
    curryRule X U K L M n (uncurryFun X U φ) t r d hd g k l =
      applyHomSectionOver X
        (sheafHomComplex X (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K).obj L) M) U W g
          n
        (t + r) d (by omega) φ (tensorComplexSection X t r (t + r) rfl k l) := by
  rw [← curryRule_degree X U (uncurryFun X U φ) t r d (t + n) rfl hd g k l, applyHomSection,
    applyHomSectionOver_applyHomSectionOver_uncurryFun, Category.id_comp, restrictSection_id]

/-- A local section of `SheafHom(Tot(K ⊗_O L), M)` is determined by its values on the local
pure tensors. -/
lemma homSection_tensor_ext
    {f f' : ((sheafHomComplex X (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K).obj L)
      M).obj.X
      n).val.obj (op U)}
    (h : ∀ (c d : ℤ) (hcd : c + n = d) (t r : ℤ) (htr : t + r = c) (W : X.C) (g : W ⟶ U)
      (k : (K.X t).val.obj (op W)) (l : (L.X r).val.obj (op W)),
      applyHomSectionOver X
          (sheafHomComplex X (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K).obj L) M) U W
            g n c d hcd
          f (tensorComplexSection X t r c htr k l) =
        applyHomSectionOver X
          (sheafHomComplex X (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K).obj L) M) U W
            g n c d hcd
          f' (tensorComplexSection X t r c htr k l)) : f = f' := by
  refine ((sheafHomComplex X (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K).obj L)
    M).sectionsEquiv
    U n).injective (Cochain.ext _ _ fun c d hcd ↦ ?_)
  exact tensorComplexOverSection_hom_ext fun t r htr W g k l ↦ h c d hcd t r htr W g k l

/-- Uncurrying is a left inverse of currying on local sections. -/
lemma uncurryFun_curryFun : uncurryFun X U (curryFun X U α) = α := by
  refine homSection_ext X (sheafHomComplex X K (sheafHomComplex X L M).obj) U n
    fun t q htq V i k ↦ ?_
  subst htq
  refine homSection_ext X (sheafHomComplex X L M) V (t + n) fun r d hrd V' j l ↦ ?_
  rw [applyHomSectionOver_applyHomSectionOver_uncurryFun,
    applyHomSectionOver_curryFun X U α (t + r) d (by omega) t r rfl (j ≫ i)
      (restrictSection X j k) l,
    ← curryRule_degree X U α t r d (t + n) rfl (by omega) (j ≫ i) (restrictSection X j k) l,
    applyHomSectionOver_restrict_comp X (sheafHomComplex X K (sheafHomComplex X L M).obj)
      U V V' i j n t (t + n) rfl α (restrictSection X j k),
    applyHomSectionOver_map X (sheafHomComplex X K (sheafHomComplex X L M).obj) V V' j n t
      (t + n) rfl (restrictSection X i α) k,
    ← applyHomSectionOver_restrict X (sheafHomComplex X K (sheafHomComplex X L M).obj) U V i n t
      (t + n) rfl α k,
    ← applyHomSectionOver_restrict X (sheafHomComplex X L M) V V' j (t + n) r d hrd
      (applyHomSectionOver X (sheafHomComplex X K (sheafHomComplex X L M).obj) U V i n t (t + n)
        rfl α k) l]

/-- Uncurrying is a right inverse of currying on local sections. -/
lemma curryFun_uncurryFun : curryFun X U (uncurryFun X U φ) = φ := by
  refine homSection_tensor_ext X U fun c d hcd t r htr W g k l ↦ ?_
  rw [applyHomSectionOver_curryFun, curryRule_uncurryFun]
  subst htr
  rfl



/-! ## Linearity of currying, and the degreewise isomorphism -/

/-- The cochain of the curried local section is the curried cochain. -/
lemma sectionsEquiv_curryFun :
    (sheafHomComplex X (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K).obj L)
      M).sectionsEquiv U n
        (curryFun X U α) = curryCochain α :=
  ((sheafHomComplex X (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K).obj L)
    M).sectionsEquiv
    U n).apply_symm_apply _

/-- Currying is injective on local sections. -/
lemma curryFun_injective
    {a a' : ((sheafHomComplex X K (sheafHomComplex X L M).obj).obj.X n).val.obj (op U)}
    (h : curryFun X U a = curryFun X U a') : a = a' := by
  rw [← uncurryFun_curryFun X U a, ← uncurryFun_curryFun X U a', h]

/-- Currying is additive. -/
lemma curryFun_add
    (a a' : ((sheafHomComplex X K (sheafHomComplex X L M).obj).obj.X n).val.obj (op U)) :
    curryFun X U (a + a') = curryFun X U a + curryFun X U a' := by
  refine homSection_tensor_ext X U fun c d hcd t r htr W g k l ↦ ?_
  rw [applyHomSectionOver_curryFun, applyHomSectionOver_add_left, applyHomSectionOver_curryFun,
    applyHomSectionOver_curryFun, curryRule_add_section]

/-- Currying is linear over the sections of the structure sheaf. -/
lemma curryFun_smul (s : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))
    (a : ((sheafHomComplex X K (sheafHomComplex X L M).obj).obj.X n).val.obj (op U)) :
    curryFun X U (s • a) = s • curryFun X U a := by
  refine homSection_tensor_ext X U fun c d hcd t r htr W g k l ↦ ?_
  rw [applyHomSectionOver_curryFun, applyHomSectionOver_smul_left, applyHomSectionOver_curryFun,
    curryRule_smul_section]

/-- Currying is compatible with restriction along an arrow of the site. -/
lemma curryFun_restrict {V : X.C} (i : V ⟶ U)
    (a : ((sheafHomComplex X K (sheafHomComplex X L M).obj).obj.X n).val.obj (op U)) :
    curryFun X V (restrictSection X i a) = restrictSection X i (curryFun X U a) := by
  refine homSection_tensor_ext X V fun c d hcd t r htr W g k l ↦ ?_
  rw [applyHomSectionOver_curryFun, curryRule_restrict_section,
    ← applyHomSectionOver_restrict_comp, applyHomSectionOver_curryFun]

/-- Uncurrying is additive. -/
lemma uncurryFun_add
    (ψ ψ' : ((sheafHomComplex X (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K).obj L)
      M).obj.X
      n).val.obj (op U)) :
    uncurryFun X U (ψ + ψ') = uncurryFun X U ψ + uncurryFun X U ψ' := by
  refine curryFun_injective X U ?_
  rw [curryFun_uncurryFun, curryFun_add, curryFun_uncurryFun, curryFun_uncurryFun]

/-- Uncurrying is linear over the sections of the structure sheaf. -/
lemma uncurryFun_smul (s : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))
    (ψ : ((sheafHomComplex X (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K).obj L)
      M).obj.X
      n).val.obj (op U)) :
    uncurryFun X U (s • ψ) = s • uncurryFun X U ψ := by
  refine curryFun_injective X U ?_
  rw [curryFun_uncurryFun, curryFun_smul, curryFun_uncurryFun]

/-- Uncurrying is compatible with restriction along an arrow of the site. -/
lemma uncurryFun_restrict {V : X.C} (i : V ⟶ U)
    (ψ : ((sheafHomComplex X (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K).obj L)
      M).obj.X
      n).val.obj (op U)) :
    uncurryFun X V (restrictSection X i ψ) = restrictSection X i (uncurryFun X U ψ) := by
  refine curryFun_injective X V ?_
  rw [curryFun_uncurryFun, curryFun_restrict, curryFun_uncurryFun]

variable (K L M n)

/-- The degree-`n` component of the currying isomorphism: the morphism of sheaves of `O`-modules
`SheafHom(K, SheafHom(L, M))^n ⟶ SheafHom(Tot(K ⊗_O L), M)^n` given on local sections by
currying. -/
def curryHom : (sheafHomComplex X K (sheafHomComplex X L M).obj).obj.X n ⟶
    (sheafHomComplex X (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K).obj L) M).obj.X n
      :=
  ⟨{ app := fun V ↦ ModuleCat.ofHom
      { toFun := fun a ↦ curryFun X V.unop a
        map_add' := fun a a' ↦ curryFun_add X V.unop a a'
        map_smul' := fun s a ↦ curryFun_smul X V.unop s a }
     naturality := by
       rintro ⟨V⟩ ⟨V'⟩ ⟨i : V' ⟶ V⟩
       exact ModuleCat.hom_ext (LinearMap.ext (curryFun_restrict X V i)) }⟩

/-- The degree-`n` component of the inverse of the currying isomorphism. -/
def uncurryHom : (sheafHomComplex X (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K).obj L)
  M).obj.X n ⟶
    (sheafHomComplex X K (sheafHomComplex X L M).obj).obj.X n :=
  ⟨{ app := fun V ↦ ModuleCat.ofHom
      { toFun := fun ψ ↦ uncurryFun X V.unop ψ
        map_add' := fun ψ ψ' ↦ uncurryFun_add X V.unop ψ ψ'
        map_smul' := fun s ψ ↦ uncurryFun_smul X V.unop s ψ }
     naturality := by
       rintro ⟨V⟩ ⟨V'⟩ ⟨i : V' ⟶ V⟩
       exact ModuleCat.hom_ext (LinearMap.ext (uncurryFun_restrict X V i)) }⟩

/-- `curryHom` acts on local sections by `curryFun`. -/
lemma curryHom_app (V : X.C)
    (a : ((sheafHomComplex X K (sheafHomComplex X L M).obj).obj.X n).val.obj (op V)) :
    (curryHom X K L M n).val.app (op V) a = curryFun X V a := rfl

/-- `uncurryHom` acts on local sections by `uncurryFun`. -/
lemma uncurryHom_app (V : X.C)
    (ψ : ((sheafHomComplex X (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K).obj L)
      M).obj.X
      n).val.obj (op V)) :
    (uncurryHom X K L M n).val.app (op V) ψ = uncurryFun X V ψ := rfl

/-- The degree-`n` component of the currying isomorphism of Stacks 0A90. -/
def curryIsoX : (sheafHomComplex X K (sheafHomComplex X L M).obj).obj.X n ≅
    (sheafHomComplex X (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K).obj L) M).obj.X n
      where
  hom := curryHom X K L M n
  inv := uncurryHom X K L M n
  hom_inv_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    rintro ⟨V⟩
    exact ModuleCat.hom_ext (LinearMap.ext fun a ↦ uncurryFun_curryFun X V a)
  inv_hom_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    rintro ⟨V⟩
    exact ModuleCat.hom_ext (LinearMap.ext fun ψ ↦ curryFun_uncurryFun X V ψ)

variable {n}

/-- `curryHom` and `uncurryHom` are the two directions of `curryIsoX`. -/
@[simp] lemma curryIsoX_hom : (curryIsoX X K L M n).hom = curryHom X K L M n := rfl

/-- `curryHom` and `uncurryHom` are the two directions of `curryIsoX`. -/
@[simp] lemma curryIsoX_inv : (curryIsoX X K L M n).inv = uncurryHom X K L M n := rfl

/-- **Stacks 0A90.** The canonical currying isomorphism of internal Hom complexes on a ringed
site: `SheafHom(K, SheafHom(L, M)) ≅ SheafHom(Tot(K ⊗_O L), M)`. -/
@[stacks 0A90 "the currying isomorphism"]
def sheafHomTensorCurryIso :
    (sheafHomComplex X K (sheafHomComplex X L M).obj).obj ≅
      (sheafHomComplex X (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K).obj L) M).obj :=
  HomologicalComplex.Hom.isoOfComponents (fun n ↦ curryIsoX X K L M n) (by
    intro i j hij
    obtain rfl : i + 1 = j := hij
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    rintro ⟨V⟩
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    refine ((sheafHomComplex X (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K).obj L)
      M).sectionsEquiv
      V (i + 1)).injective ?_
    rw [comp_val_app_apply', comp_val_app_apply']
    change (sheafHomComplex X (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K).obj L)
      M).sectionsEquiv
        V (i + 1)
        (((sheafHomComplex X (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K).obj L)
          M).obj.d i
          (i + 1)).val.app (op V) (curryFun X V a)) =
      (sheafHomComplex X (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K).obj L)
        M).sectionsEquiv
        V (i + 1)
        (curryFun X V (((sheafHomComplex X K (sheafHomComplex X L M).obj).obj.d i
          (i + 1)).val.app (op V) a))
    rw [SheafHomComplex.sectionsEquiv_d, sectionsEquiv_curryFun, sectionsEquiv_curryFun,
      curryCochain_delta])


/-- The degreewise components of the currying isomorphism. -/
@[simp] lemma sheafHomTensorCurryIso_hom_f (n : ℤ) :
    (sheafHomTensorCurryIso X K L M).hom.f n = curryHom X K L M n := rfl

/-- The degreewise components of the inverse of the currying isomorphism. -/
@[simp] lemma sheafHomTensorCurryIso_inv_f (n : ℤ) :
    (sheafHomTensorCurryIso X K L M).inv.f n = uncurryHom X K L M n := rfl

end AlgebraicGeometry.RingedSite

end
