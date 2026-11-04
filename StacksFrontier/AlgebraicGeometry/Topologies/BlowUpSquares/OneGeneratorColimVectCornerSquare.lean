module

public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.OneGeneratorColimVectEssSurjFunctor

/-!
# The calculus of restriction along commuting squares, for the corner of Stacks 0EXC

This file develops the part of the pseudofunctor calculus of
`AlgebraicGeometry.Scheme.Vect.pullback` which the compatibility over the exceptional corner of
Stacks Tag 0EXC needs: the comparison `AlgebraicGeometry.Scheme.Vect.pullbackCongr` of the
restrictions along two equal morphisms composes and transposes as expected, the comparison
`AlgebraicGeometry.vectPullbackSquareIso` attached to a commuting square only depends on its
four morphisms up to those comparisons, and the comparison attached to a horizontal pasting of
two squares is the pasting of the two comparisons.

It also records the two recursion equations of
`AlgebraicGeometry.frobeniusPullbackIterIso`, the comparison of the `k`-fold Frobenius pullback
with restriction along the `k`-fold absolute Frobenius, at an object, and identifies the
**iterated Frobenius comparison** `CategoryTheory.EndoColim.squareIter` of
`AlgebraicGeometry.frobeniusVectPullbackIso` with the comparison attached to the naturality
square of the `k`-fold absolute Frobenius.

## Main results

* `AlgebraicGeometry.vectPullbackCongr_trans_hom_app` and
  `AlgebraicGeometry.vectPullbackCongr_inv_app_eq`: the comparison of the restrictions along two
  equal morphisms is compatible with transitivity and with symmetry of the equality.
* `AlgebraicGeometry.vectPullbackSquareIso_congr_hom_app`: **the comparison attached to a
  commuting square depends on its four morphisms only up to
  `AlgebraicGeometry.Scheme.Vect.pullbackCongr`.**
* `AlgebraicGeometry.vectPullbackSquareIso_paste_app`: **the comparison attached to a horizontal
  pasting of two commuting squares is the pasting of the two comparisons**, on vector bundles.
* `AlgebraicGeometry.vectPullbackSquareIso_id_hom_app`: the comparison attached to the square
  expressing that a morphism commutes with the two identities is the unit comparison of the
  pullback pseudofunctor.
* `AlgebraicGeometry.vectCornerFlat`: **the compatibility over the exceptional corner, with the
  iteration removed and the affine comparison abstracted into one hypothesis** — pure
  pseudofunctor calculus for the two commuting squares of Example 0EVG, their two Frobenius
  naturality squares and the square comparing the two restrictions to the corner.
* `AlgebraicGeometry.squareIter_frobeniusVectPullbackIso_hom`: **the iterated Frobenius
  comparison `CategoryTheory.EndoColim.squareIter` of
  `AlgebraicGeometry.frobeniusVectPullbackIso` is the comparison attached to the naturality
  square of the `k`-fold absolute Frobenius**, read through
  `AlgebraicGeometry.frobeniusPullbackIterIso`. This is what removes the iteration from the
  compatibility over the exceptional corner.

## Implementation notes

Every statement here keeps the four morphisms of the square, and the vector bundle, as
*variables*. That is not a matter of taste: `AlgebraicGeometry.Scheme.Modules.pullbackCongr` is
an `CategoryTheory.eqToIso`, so the kernel's K-like reduction of its components asks whether the
two morphisms of the square are definitionally equal, and for the concrete morphisms of Example
0EVG — a composite `Spec.map φ ≫ Spec.map ψ` against `Spec.map (φ ≫ ψ)` — answering that
question exhausts the kernel's budget. With the morphisms left variable the question is settled
at once, and the general statements are then *instantiated*, which costs nothing.

A second, unrelated restriction shapes the proofs here. `AlgebraicGeometry.Scheme.Vect` is a
full subcategory cut out by `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree` with its
universe arguments written out, and a goal mentioning
`(AlgebraicGeometry.frobeniusPullback X p hX).endoIter k` is therefore not type-correct at
`implicit` transparency: `simp only [Category.assoc]` reports no progress on it, and `rw` with
`CategoryTheory.Category.assoc` or `CategoryTheory.Category.id_comp` fails to find its pattern,
because the unifier may not unfold `AlgebraicGeometry.frobeniusPullbackIter`. The inductive step
below therefore does all of its reassociation inside
`AlgebraicGeometry.comp_step_aux`, a statement of pure category theory whose ingredients are all
variables, and the pieces are fed to it by `exact`, which is checked at default transparency.

## References

* [Stacks Project, Tag 0CC7](https://stacks.math.columbia.edu/tag/0CC7)
* [Stacks Project, Tag 0EXA](https://stacks.math.columbia.edu/tag/0EXA)
* [Stacks Project, Tag 0EXC](https://stacks.math.columbia.edu/tag/0EXC)
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.Frobenius

universe u

namespace AlgebraicGeometry

/-! ### Reassociation, on variables -/

section Reassoc

variable {C : Type*} [Category C] {V W X Y Z : C}

/-- `CategoryTheory.Category.assoc` for a three-fold composite with a trailing morphism, with
every morphism a variable. -/
lemma comp_assoc₃ (a : V ⟶ W) (b : W ⟶ X) (c : X ⟶ Y) (d : Y ⟶ Z) :
    (a ≫ b ≫ c) ≫ d = a ≫ b ≫ c ≫ d := by simp

end Reassoc

/-! ### Restriction along equal morphisms -/

section Congr

variable {X Y : Scheme.{u}}

/-- **The comparison of the restrictions along two equal morphisms is compatible with
transitivity.** The composite equality is taken as a hypothesis rather than built from the two
given ones, because the built proof term is what the kernel has to recheck at every use. -/
lemma vectPullbackCongr_trans_hom_app {g h k : X ⟶ Y} (e : g = h) (e' : h = k) (e'' : g = k)
    (M : Y.Vect) :
    (Scheme.Vect.pullbackCongr e).hom.app M ≫ (Scheme.Vect.pullbackCongr e').hom.app M =
      (Scheme.Vect.pullbackCongr e'').hom.app M := by
  subst e
  subst e'
  obtain rfl : e'' = rfl := rfl
  simp only [vectPullbackCongr_refl_hom_app, Category.comp_id]

/-- **The inverse comparison of the restrictions along two equal morphisms is the comparison for
the symmetric equality.** -/
lemma vectPullbackCongr_inv_app_eq {g h : X ⟶ Y} (e : g = h) (e' : h = g) (M : Y.Vect) :
    (Scheme.Vect.pullbackCongr e).inv.app M = (Scheme.Vect.pullbackCongr e').hom.app M := by
  subst e
  obtain rfl : e' = rfl := rfl
  simp only [vectPullbackCongr_refl_inv_app, vectPullbackCongr_refl_hom_app]

/-- **The comparison of the restrictions along two equal morphisms is the identity when the two
morphisms are the same term**, on all sheaves of modules. -/
lemma modulesPullbackCongr_refl_hom_app (g : X ⟶ Y) (N : Y.Modules) :
    (Scheme.Modules.pullbackCongr (rfl : g = g)).hom.app N = 𝟙 _ := by
  simp [Scheme.Modules.pullbackCongr]

/-- **The inverse comparison of the restrictions along two equal morphisms is the comparison for
the symmetric equality**, on all sheaves of modules. -/
lemma modulesPullbackCongr_inv_app_eq {g h : X ⟶ Y} (e : g = h) (e' : h = g) (N : Y.Modules) :
    (Scheme.Modules.pullbackCongr e).inv.app N =
      (Scheme.Modules.pullbackCongr e').hom.app N := by
  subst e
  obtain rfl : e' = rfl := rfl
  simp [Scheme.Modules.pullbackCongr]

/-- **The unit coherence of the pullback pseudofunctor, read on an object.** The transport along
the equality `𝟙 X ≫ g = g ≫ 𝟙 Y` identifies the two unit comparisons. -/
lemma modulesPullbackCongr_id_comp (g : X ⟶ Y) (h : 𝟙 X ≫ g = g ≫ 𝟙 Y) (N : Y.Modules) :
    (Scheme.Modules.pullbackCongr h).hom.app N ≫
        (Scheme.Modules.pullbackComp g (𝟙 Y)).inv.app N ≫
          (Scheme.Modules.pullback g).map ((Scheme.Modules.pullbackId Y).hom.app N) =
      (Scheme.Modules.pullbackComp (𝟙 X) g).inv.app N ≫
        (Scheme.Modules.pullbackId X).hom.app ((Scheme.Modules.pullback g).obj N) := by
  have hL := NatTrans.congr_app (Scheme.Modules.pseudofunctor_left_unitality (f := g)) N
  have hR := NatTrans.congr_app (Scheme.Modules.pseudofunctor_right_unitality (f := g)) N
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_hom_app, eqToHom_app] at hL hR
  rw [@Category.comp_id _ _ _ ((Scheme.Modules.pullback g).obj N)
    ((Scheme.Modules.pullback g).map ((Scheme.Modules.pullbackId Y).hom.app N))] at hL
  rw [@Category.comp_id _ _ _ ((Scheme.Modules.pullback g).obj N)
    ((Scheme.Modules.pullbackId X).hom.app ((Scheme.Modules.pullback g).obj N))] at hR
  rw [hL, hR]
  simp [Scheme.Modules.pullbackCongr]

end Congr

/-! ### The comparison attached to a commuting square -/

section Square

variable {W X Y Z : Scheme.{u}}

/-- **The comparison attached to a commuting square of schemes, as a composite of
pseudofunctoriality comparisons.** This is the counterpart of
`AlgebraicGeometry.vectPullbackSquareIso_inv_app_eq` for the isomorphism itself. -/
lemma vectPullbackSquareIso_hom_app_eq {a : W ⟶ Y} {b : Y ⟶ X} {c : W ⟶ Z} {d : Z ⟶ X}
    (h : a ≫ b = c ≫ d) (M : X.Vect) :
    (vectPullbackSquareIso h).hom.app M =
      (Scheme.Vect.pullbackComp a b).hom.app M ≫
        (Scheme.Vect.pullbackCongr h).hom.app M ≫
          (Scheme.Vect.pullbackComp c d).inv.app M :=
  ObjectProperty.hom_ext _ (by simp [modulesPullbackSquareIso])

/-- **The comparison attached to a commuting square of schemes depends on the four morphisms of
the square only up to the comparison of the restrictions along equal morphisms.** -/
lemma vectPullbackSquareIso_congr_hom_app {a a' : W ⟶ Y} {b b' : Y ⟶ X} {c c' : W ⟶ Z}
    {d d' : Z ⟶ X} (ea : a = a') (eb : b = b') (ec : c = c') (ed : d = d')
    (h : a ≫ b = c ≫ d) (h' : a' ≫ b' = c' ≫ d') (M : X.Vect) :
    (vectPullbackSquareIso h).hom.app M =
      (Scheme.Vect.pullback a).map ((Scheme.Vect.pullbackCongr eb).hom.app M) ≫
        (Scheme.Vect.pullbackCongr ea).hom.app ((Scheme.Vect.pullback b').obj M) ≫
          (vectPullbackSquareIso h').hom.app M ≫
            (Scheme.Vect.pullback c').map ((Scheme.Vect.pullbackCongr ed).inv.app M) ≫
              (Scheme.Vect.pullbackCongr ec).inv.app ((Scheme.Vect.pullback d).obj M) := by
  subst ea
  subst eb
  subst ec
  subst ed
  obtain rfl : h' = h := rfl
  simp only [vectPullbackCongr_refl_hom_app, vectPullbackCongr_refl_inv_app,
    CategoryTheory.Functor.map_id]
  exact (Category.id_comp _).symm.trans (congrArg _ (Category.comp_id _).symm)

variable {X' Y' Z' : Scheme.{u}}

/-- **The comparison attached to a horizontal pasting of two commuting squares of schemes is the
pasting of the two comparisons, on vector bundles.** This is
`AlgebraicGeometry.modulesPullbackSquareIso_paste_app` transported to the full subcategories of
finite locally free modules. -/
theorem vectPullbackSquareIso_paste_app (g : X ⟶ Y) (h : Y ⟶ Z) (k : X ⟶ X') (l : Y ⟶ Y')
    (m : Z ⟶ Z') (g' : X' ⟶ Y') (h' : Y' ⟶ Z') (w₁ : g ≫ l = k ≫ g')
    (w₂ : h ≫ m = l ≫ h') (w : (g ≫ h) ≫ m = k ≫ g' ≫ h') (M : Z'.Vect) :
    (Scheme.Vect.pullbackComp g h).hom.app ((Scheme.Vect.pullback m).obj M) ≫
        (vectPullbackSquareIso w).hom.app M =
      (Scheme.Vect.pullback g).map ((vectPullbackSquareIso w₂).hom.app M) ≫
        (vectPullbackSquareIso w₁).hom.app ((Scheme.Vect.pullback h').obj M) ≫
          (Scheme.Vect.pullback k).map ((Scheme.Vect.pullbackComp g' h').hom.app M) :=
  ObjectProperty.hom_ext _ (by
    simpa using modulesPullbackSquareIso_paste_app g h k l m g' h' w₁ w₂ w M.obj)

end Square

/-! ### Restriction along an identity, and the inverse comparison -/

section Unit

variable {X Y : Scheme.{u}}

/-- **The comparison attached to a commuting square of schemes is the inverse of the comparison
attached to the same square read the other way round.** -/
lemma vectPullbackSquareIso_inv_app_eq_symm {W Z : Scheme.{u}} {a : W ⟶ Y} {b : Y ⟶ X}
    {c : W ⟶ Z} {d : Z ⟶ X} (h : a ≫ b = c ≫ d) (h' : c ≫ d = a ≫ b) (M : X.Vect) :
    (vectPullbackSquareIso h).inv.app M = (vectPullbackSquareIso h').hom.app M :=
  ObjectProperty.hom_ext _ (by
    simp only [vectPullbackSquareIso_inv_app_hom, vectPullbackSquareIso_hom_app_hom,
      modulesPullbackSquareIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      NatTrans.comp_app, Category.assoc]
    rw [modulesPullbackCongr_inv_app_eq h h'])

/-- The comparison attached to the square expressing that `g` commutes with the two identities,
on all sheaves of modules: it is the unit comparison of the pullback pseudofunctor. -/
lemma modulesPullbackSquareIso_id_hom_app (g : X ⟶ Y) (h : 𝟙 X ≫ g = g ≫ 𝟙 Y)
    (N : Y.Modules) :
    (modulesPullbackSquareIso h).hom.app N =
      (Scheme.Modules.pullbackId X).hom.app ((Scheme.Modules.pullback g).obj N) ≫
        (Scheme.Modules.pullback g).map ((Scheme.Modules.pullbackId Y).inv.app N) := by
  rw [modulesPullbackSquareIso]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [← cancel_mono ((Scheme.Modules.pullback g).map
    ((Scheme.Modules.pullbackId Y).hom.app N)), Category.assoc, Category.assoc,
    Category.assoc, modulesPullbackCongr_id_comp g h N, Iso.hom_inv_id_app_assoc,
    ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app]
  simp

/-- **The comparison attached to the square expressing that `g` commutes with the two
identities** is the unit comparison of the pullback pseudofunctor, on vector bundles. -/
lemma vectPullbackSquareIso_id_hom_app (g : X ⟶ Y) (h : 𝟙 X ≫ g = g ≫ 𝟙 Y) (M : Y.Vect) :
    (vectPullbackSquareIso h).hom.app M =
      (Scheme.Vect.pullbackId X).hom.app ((Scheme.Vect.pullback g).obj M) ≫
        (Scheme.Vect.pullback g).map ((Scheme.Vect.pullbackId Y).inv.app M) :=
  ObjectProperty.hom_ext _ (by simpa using modulesPullbackSquareIso_id_hom_app g h M.obj)

end Unit

/-! ### The iterated Frobenius comparison -/

section Iter

variable (p : ℕ) [Fact p.Prime] {X : Scheme.{u}} (hX : IsInCharacteristic X p)

/-- The comparison of the `0`-fold Frobenius pullback with restriction along the `0`-fold
absolute Frobenius, at an object. -/
lemma frobeniusPullbackIterIso_zero_hom_app (Z : X.Vect) :
    (frobeniusPullbackIterIso X p hX 0).hom.app Z =
      (Scheme.Vect.pullbackId X).inv.app Z ≫
        (Scheme.Vect.pullbackCongr (absoluteFrobeniusPow_zero X p hX).symm).hom.app Z := by
  rw [frobeniusPullbackIterIso]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  exact Category.id_comp _

/-- The comparison of the `k + 1`-fold Frobenius pullback with restriction along the
`k + 1`-fold absolute Frobenius, at an object. -/
lemma frobeniusPullbackIterIso_succ_hom_app (k : ℕ) (Z : X.Vect) :
    (frobeniusPullbackIterIso X p hX (k + 1)).hom.app Z =
      (Scheme.Vect.pullback (absoluteFrobenius X p hX)).map
          ((frobeniusPullbackIterIso X p hX k).hom.app Z) ≫
        (Scheme.Vect.pullbackComp (absoluteFrobenius X p hX)
            (absoluteFrobeniusPow X p hX k)).hom.app Z ≫
          (Scheme.Vect.pullbackCongr
            (absoluteFrobeniusPow_succ_eq_comp X p hX k).symm).hom.app Z := by
  rw [frobeniusPullbackIterIso]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app]
  exact Category.id_comp _

end Iter

/-! ### The iterated Frobenius comparison as the comparison of a square -/

section IterSquare

variable {X Y : Scheme.{u}}

/-- For endomorphisms `aX` of `X` and `aY` of `Y` equal to the identities and commuting with
`g : X ⟶ Y`, the restriction along `g` of the unit comparison of `aY` agrees with the unit
comparison of `aX` followed by the comparison `vectPullbackSquareIso` of the square. -/
lemma vectPullbackSquareIso_unit_aux (g : X ⟶ Y) (aX : X ⟶ X) (aY : Y ⟶ Y)
    (eX : 𝟙 X = aX) (eY : 𝟙 Y = aY) (h : aX ≫ g = g ≫ aY) (M : Y.Vect) :
    (Scheme.Vect.pullback g).map ((Scheme.Vect.pullbackId Y).inv.app M ≫
          (Scheme.Vect.pullbackCongr eY).hom.app M) =
      ((Scheme.Vect.pullbackId X).inv.app ((Scheme.Vect.pullback g).obj M) ≫
          (Scheme.Vect.pullbackCongr eX).hom.app ((Scheme.Vect.pullback g).obj M)) ≫
        (vectPullbackSquareIso h).hom.app M := by
  subst eX
  subst eY
  rw [vectPullbackCongr_refl_hom_app, vectPullbackCongr_refl_hom_app, Category.comp_id,
    Category.comp_id, vectPullbackSquareIso_id_hom_app, Iso.inv_hom_id_app_assoc]

/-- Given squares `fX ≫ g = g ≫ fY`, `aX ≫ g = g ≫ aY` and `bX ≫ g = g ≫ bY` with
`fX ≫ aX = bX` and `fY ≫ aY = bY`, the comparison `vectPullbackSquareIso` of the third square,
precomposed with the composition comparison of `fX` and `aX`, is the pasting of the comparisons
of the first two, followed by the restriction along `g` of the composition comparison of `fY`
and `aY`. -/
lemma vectPullbackSquareIso_succ_aux (g : X ⟶ Y) (fX : X ⟶ X) (fY : Y ⟶ Y) (aX : X ⟶ X)
    (aY : Y ⟶ Y) (bX : X ⟶ X) (bY : Y ⟶ Y) (eX : fX ≫ aX = bX) (eY : fY ≫ aY = bY)
    (hf : fX ≫ g = g ≫ fY) (ha : aX ≫ g = g ≫ aY) (hb : bX ≫ g = g ≫ bY) (M : Y.Vect) :
    (Scheme.Vect.pullbackComp fX aX).hom.app ((Scheme.Vect.pullback g).obj M) ≫
        (Scheme.Vect.pullbackCongr eX).hom.app ((Scheme.Vect.pullback g).obj M) ≫
          (vectPullbackSquareIso hb).hom.app M =
      (Scheme.Vect.pullback fX).map ((vectPullbackSquareIso ha).hom.app M) ≫
        (vectPullbackSquareIso hf).hom.app ((Scheme.Vect.pullback aY).obj M) ≫
          (Scheme.Vect.pullback g).map ((Scheme.Vect.pullbackComp fY aY).hom.app M ≫
            (Scheme.Vect.pullbackCongr eY).hom.app M) := by
  subst eX
  subst eY
  rw [vectPullbackCongr_refl_hom_app, vectPullbackCongr_refl_hom_app, Category.id_comp,
    Category.comp_id]
  exact vectPullbackSquareIso_paste_app fX aX g g g fY aY hf ha hb M

/-- The inverse of the comparison `frobeniusVectPullbackIso` at a vector bundle is the
comparison `vectPullbackSquareIso` attached to the naturality square of the absolute
Frobenius. -/
lemma frobeniusVectPullbackIso_inv_app_eq (p : ℕ) [Fact p.Prime]
    (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p) (g : X ⟶ Y)
    (h : absoluteFrobenius X p hX ≫ g = g ≫ absoluteFrobenius Y p hY) (M : Y.Vect) :
    (frobeniusVectPullbackIso g p hX hY).inv.app M = (vectPullbackSquareIso h).hom.app M :=
  vectPullbackSquareIso_inv_app_eq_symm (absoluteFrobenius_naturality g p hX hY).symm h M

/-- The bookkeeping of the inductive step of
`AlgebraicGeometry.squareIter_frobeniusVectPullbackIso_hom`, as a statement of pure category
theory. -/
lemma comp_step_aux {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {U₁ U₂ U₃ U₄ : C} (s : U₁ ⟶ U₂) (m : U₂ ⟶ U₃) (i : U₁ ⟶ U₄) (q : U₄ ⟶ U₃)
    (ih : s ≫ m = i ≫ q) {T₁ T₂ T₃ R P : D} (b : F.obj U₂ ⟶ T₁) (c : T₁ ⟶ T₂) (d : T₂ ⟶ T₃)
    (b₂ : F.obj U₃ ⟶ T₂) (hnat : F.map m ≫ b₂ = b ≫ c) (X₁ : F.obj U₄ ⟶ R) (X₂ : R ⟶ P)
    (S : F.obj U₁ ⟶ T₁) (M : T₁ ⟶ T₃) (I : F.obj U₁ ⟶ P) (D' : P ⟶ T₃)
    (e₁ : S = F.map s ≫ b) (e₂ : M = c ≫ d)
    (e₃ : I ≫ D' = F.map i ≫ X₁ ≫ X₂ ≫ D')
    (haux : X₁ ≫ X₂ ≫ D' = F.map q ≫ b₂ ≫ d) :
    S ≫ M = I ≫ D' := by
  subst e₁
  subst e₂
  rw [e₃, haux, Category.assoc, ← Category.assoc b c d, ← hnat]
  simp only [Category.assoc]
  rw [← Category.assoc (F.map s) (F.map m) (b₂ ≫ d), ← F.map_comp, ih, F.map_comp]
  simp only [Category.assoc]

/-- **The iterated Frobenius comparison is the comparison attached to the naturality square of
the `k`-fold absolute Frobenius.** -/
theorem squareIter_frobeniusVectPullbackIso_hom (p : ℕ) [Fact p.Prime]
    (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p) (g : X ⟶ Y) :
    ∀ (k : ℕ) (E : Y.Vect),
      (EndoColim.squareIter (frobeniusPullback Y p hY) (frobeniusPullback X p hX)
            (Scheme.Vect.pullback g) (frobeniusVectPullbackIso g p hX hY) k E).hom ≫
          (Scheme.Vect.pullback g).map ((frobeniusPullbackIterIso Y p hY k).hom.app E) =
        (frobeniusPullbackIterIso X p hX k).hom.app ((Scheme.Vect.pullback g).obj E) ≫
          (vectPullbackSquareIso (absoluteFrobeniusPow_naturality g p hX hY k)).hom.app E
  | 0, E => by
      rw [show (EndoColim.squareIter (frobeniusPullback Y p hY) (frobeniusPullback X p hX)
              (Scheme.Vect.pullback g) (frobeniusVectPullbackIso g p hX hY) 0 E).hom ≫
            (Scheme.Vect.pullback g).map ((frobeniusPullbackIterIso Y p hY 0).hom.app E) =
          (Scheme.Vect.pullback g).map ((frobeniusPullbackIterIso Y p hY 0).hom.app E) from
          Category.id_comp _,
        frobeniusPullbackIterIso_zero_hom_app, frobeniusPullbackIterIso_zero_hom_app]
      exact vectPullbackSquareIso_unit_aux g _ _ (absoluteFrobeniusPow_zero X p hX).symm
        (absoluteFrobeniusPow_zero Y p hY).symm _ E
  | k + 1, E => by
      have ih := squareIter_frobeniusVectPullbackIso_hom p hX hY g k E
      have hw₁ : absoluteFrobenius X p hX ≫ g = g ≫ absoluteFrobenius Y p hY :=
        absoluteFrobenius_naturality g p hX hY
      have haux := vectPullbackSquareIso_succ_aux g (absoluteFrobenius X p hX)
        (absoluteFrobenius Y p hY) (absoluteFrobeniusPow X p hX k)
        (absoluteFrobeniusPow Y p hY k) (absoluteFrobeniusPow X p hX (k + 1))
        (absoluteFrobeniusPow Y p hY (k + 1))
        (absoluteFrobeniusPow_succ_eq_comp X p hX k).symm
        (absoluteFrobeniusPow_succ_eq_comp Y p hY k).symm hw₁
        (absoluteFrobeniusPow_naturality g p hX hY k)
        (absoluteFrobeniusPow_naturality g p hX hY (k + 1)) E
      have hnat := (vectPullbackSquareIso hw₁).hom.naturality
        ((frobeniusPullbackIterIso Y p hY k).hom.app E)
      have e1 : (EndoColim.squareIter (frobeniusPullback Y p hY) (frobeniusPullback X p hX)
              (Scheme.Vect.pullback g) (frobeniusVectPullbackIso g p hX hY) (k + 1) E).hom =
          (frobeniusPullback X p hX).map
              (EndoColim.squareIter (frobeniusPullback Y p hY) (frobeniusPullback X p hX)
                (Scheme.Vect.pullback g) (frobeniusVectPullbackIso g p hX hY) k E).hom ≫
            (vectPullbackSquareIso hw₁).hom.app
              (((frobeniusPullback Y p hY).endoIter k).obj E) := by
        rw [EndoColim.squareIter_succ_hom, frobeniusVectPullbackIso_inv_app_eq p hX hY g hw₁]
        rfl
      have e2 : (Scheme.Vect.pullback g).map
            ((frobeniusPullbackIterIso Y p hY (k + 1)).hom.app E) =
          (Scheme.Vect.pullback g).map ((Scheme.Vect.pullback (absoluteFrobenius Y p hY)).map
              ((frobeniusPullbackIterIso Y p hY k).hom.app E)) ≫
            (Scheme.Vect.pullback g).map
              ((Scheme.Vect.pullbackComp (absoluteFrobenius Y p hY)
                  (absoluteFrobeniusPow Y p hY k)).hom.app E ≫
                (Scheme.Vect.pullbackCongr
                  (absoluteFrobeniusPow_succ_eq_comp Y p hY k).symm).hom.app E) := by
        rw [frobeniusPullbackIterIso_succ_hom_app]
        exact CategoryTheory.Functor.map_comp _ _ _
      have e3 : (frobeniusPullbackIterIso X p hX (k + 1)).hom.app
              ((Scheme.Vect.pullback g).obj E) ≫
            (vectPullbackSquareIso
              (absoluteFrobeniusPow_naturality g p hX hY (k + 1))).hom.app E =
          (Scheme.Vect.pullback (absoluteFrobenius X p hX)).map
              ((frobeniusPullbackIterIso X p hX k).hom.app
                ((Scheme.Vect.pullback g).obj E)) ≫
            (Scheme.Vect.pullbackComp (absoluteFrobenius X p hX)
                  (absoluteFrobeniusPow X p hX k)).hom.app
                ((Scheme.Vect.pullback g).obj E) ≫
              (Scheme.Vect.pullbackCongr
                  (absoluteFrobeniusPow_succ_eq_comp X p hX k).symm).hom.app
                ((Scheme.Vect.pullback g).obj E) ≫
                (vectPullbackSquareIso
                  (absoluteFrobeniusPow_naturality g p hX hY (k + 1))).hom.app E := by
        rw [frobeniusPullbackIterIso_succ_hom_app]
        exact comp_assoc₃ _ _ _ _
      exact comp_step_aux (Scheme.Vect.pullback (absoluteFrobenius X p hX)) _ _ _ _ ih _ _ _ _
        hnat _ _ _ _ _ _ e1 e2 e3 haux

end IterSquare

/-! ### The flat coherence over the exceptional corner -/

section Flat

variable {W X Y Z : Scheme.{u}}

/-- Replacing two of the four morphisms of a commuting square by equal ones changes the
comparison `vectPullbackSquareIso` by the comparisons `Scheme.Vect.pullbackCongr` of the
restrictions along them. -/
lemma vectPullbackSquareIso_congr₂_hom_app {a a' : W ⟶ Y} {b : Y ⟶ X} {c : W ⟶ Z}
    {d d' : Z ⟶ X} (ea : a = a') (ed : d = d')
    (h : a ≫ b = c ≫ d) (h' : a' ≫ b = c ≫ d') (M : X.Vect) :
    (vectPullbackSquareIso h).hom.app M =
      (Scheme.Vect.pullbackCongr ea).hom.app ((Scheme.Vect.pullback b).obj M) ≫
        (vectPullbackSquareIso h').hom.app M ≫
          (Scheme.Vect.pullback c).map ((Scheme.Vect.pullbackCongr ed).inv.app M) := by
  rw [vectPullbackSquareIso_congr_hom_app ea rfl rfl ed h h' M]
  simp only [vectPullbackCongr_refl_hom_app, vectPullbackCongr_refl_inv_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

variable {R' A' S₁' S₂' T' : Scheme.{u}}

/-- **The compatibility over the exceptional corner, with the iteration removed.** Given
commuting squares `c ≫ b = P₁ ≫ ρ₁` and `m ≫ b = P₂ ≫ ρ₂`, their naturality squares along `σ`
and `τ`, the square `τ ≫ m = σ ≫ c` and morphisms `jc`, `jm` and `w` related by `H`, the two
composites from the restriction of `E` along `σ ≫ c` to the restriction of `Ec` along `P ≫ σ`
given by the comparisons `vectPullbackSquareIso` agree. -/
theorem vectCornerFlat (b : A' ⟶ R') (c : S₁' ⟶ A') (m : S₂' ⟶ A') (σ : T' ⟶ S₁')
    (τ : T' ⟶ S₂') (ρ₁ : S₁' ⟶ R') (ρ₂ : S₂' ⟶ R') (P₁ : S₁' ⟶ S₁') (P₂ : S₂' ⟶ S₂')
    (P : T' ⟶ T') (hC : c ≫ b = P₁ ≫ ρ₁) (hM : m ≫ b = P₂ ≫ ρ₂) (hS : τ ≫ m = σ ≫ c)
    (hFC : σ ≫ P₁ = P ≫ σ) (hFM : τ ≫ P₂ = P ≫ τ) (hv : σ ≫ ρ₁ = τ ≫ ρ₂)
    (hOutC : (σ ≫ c) ≫ b = P ≫ σ ≫ ρ₁) (hOutM : (τ ≫ m) ≫ b = P ≫ τ ≫ ρ₂)
    (E : R'.Vect) (Ec : S₁'.Vect) (Em : S₂'.Vect)
    (jc : (Scheme.Vect.pullback ρ₁).obj E ⟶ Ec) (jm : (Scheme.Vect.pullback ρ₂).obj E ⟶ Em)
    (w : (Scheme.Vect.pullback τ).obj Em ⟶ (Scheme.Vect.pullback σ).obj Ec)
    (H : (Scheme.Vect.pullback σ).map jc =
      ((Scheme.Vect.pullbackComp σ ρ₁).hom.app E ≫ (Scheme.Vect.pullbackCongr hv).hom.app E ≫
          (Scheme.Vect.pullbackComp τ ρ₂).inv.app E) ≫
        (Scheme.Vect.pullback τ).map jm ≫ w) :
    (Scheme.Vect.pullback σ).map ((vectPullbackSquareIso hC).hom.app E ≫
          (Scheme.Vect.pullback P₁).map jc) ≫ (vectPullbackSquareIso hFC).hom.app Ec =
      (vectPullbackSquareIso hS).inv.app ((Scheme.Vect.pullback b).obj E) ≫
        (Scheme.Vect.pullback τ).map ((vectPullbackSquareIso hM).hom.app E ≫
            (Scheme.Vect.pullback P₂).map jm) ≫
          (vectPullbackSquareIso hFM).hom.app Em ≫ (Scheme.Vect.pullback P).map w := by
  have hnatC := (vectPullbackSquareIso hFC).hom.naturality jc
  have hnatM := (vectPullbackSquareIso hFM).hom.naturality jm
  simp only [Functor.comp_map] at hnatC hnatM
  have hM2 : (Scheme.Vect.pullback τ).map ((vectPullbackSquareIso hM).hom.app E) ≫
        (vectPullbackSquareIso hFM).hom.app ((Scheme.Vect.pullback ρ₂).obj E) =
      (Scheme.Vect.pullbackComp τ m).hom.app ((Scheme.Vect.pullback b).obj E) ≫
        (vectPullbackSquareIso hOutM).hom.app E ≫
          (Scheme.Vect.pullback P).map ((Scheme.Vect.pullbackComp τ ρ₂).inv.app E) := by
    rw [← cancel_mono ((Scheme.Vect.pullback P).map
      ((Scheme.Vect.pullbackComp τ ρ₂).hom.app E))]
    simp only [Category.assoc, ← CategoryTheory.Functor.map_comp]
    rw [Iso.inv_hom_id_app]
    simp only [CategoryTheory.Functor.map_id]
    exact (vectPullbackSquareIso_paste_app τ m P P₂ b τ ρ₂ hFM hM hOutM E).symm
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [hnatC, reassoc_of% hnatM,
    vectPullbackSquareIso_inv_app_eq hS ((Scheme.Vect.pullback b).obj E), H]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← reassoc_of% (vectPullbackSquareIso_paste_app σ c P P₁ b σ ρ₁ hFC hC hOutC E),
    vectPullbackSquareIso_congr₂_hom_app hS.symm hv hOutC hOutM E,
    ← vectPullbackCongr_inv_app_eq hS hS.symm, reassoc_of% hM2, Iso.inv_hom_id_app_assoc]
  simp only [Category.assoc]
  have hcc : (Scheme.Vect.pullback P).map ((Scheme.Vect.pullbackCongr hv).inv.app E) ≫
      (Scheme.Vect.pullback P).map ((Scheme.Vect.pullbackCongr hv).hom.app E) = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  rw [reassoc_of% hcc]

end Flat

end AlgebraicGeometry

end
