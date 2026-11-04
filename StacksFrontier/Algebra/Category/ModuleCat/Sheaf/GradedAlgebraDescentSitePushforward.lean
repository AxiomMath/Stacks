module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraDescentHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedSitePushforward

/-!
# Descent of a sheaf of graded algebras commutes with pushforward along a continuous functor

Let `F : C ⥤ D` be a continuous functor of sites, let `α : R ⟶ R'` be a locally surjective
morphism of sheaves of rings on `D` and `β : S ⟶ S'` one on `C`, and let
`φ : S ⟶ F_* R` and `φ' : S' ⟶ F_* R'` be structure maps making the square

`φ ≫ F_* α = β ≫ φ'`

commute. Then the two ways of carrying a sheaf of graded `R`-algebras annihilated by the kernel
of `α` to a sheaf of graded `S'`-algebras agree: descending along `α` and then pushing forward
along `φ'` gives the same algebra as pushing forward along `φ` and then descending along `β`.

`SheafOfModules.GradedAlgebra.pushforward` carries an algebra off a site onto another site
presenting the same topos, and `SheafOfModules.GradedAlgebra.descend` descends one along a
quotient of the ring sheaf; the statement is that these two operations commute.

## Main definitions

* `Stacks.SheafOfModules.ChangeOfRings.liftedSheafSitePushforwardIso`: **the module-level
  transport** — the pushforward of a descended sheaf of modules is the descent of its
  pushforward.
* `SheafOfModules.GradedAlgebra.descendSitePushforwardHom`: **the transport**, as a unital
  homomorphism of sheaves of graded `S'`-algebras, and
  `SheafOfModules.GradedAlgebra.descendSitePushforwardIso`, the resulting isomorphism.
* `SheafOfModules.GradedAlgebra.descendOverHom` and
  `SheafOfModules.GradedAlgebra.descendOverIso`: **the transport across restriction to a slice
  site**, the case `F = Over.forget U`.

## Main statements

* `Stacks.SheafOfModules.ChangeOfRings.smul_pushforward_eq_zero`: the pushforward of an
  annihilated sheaf of modules is annihilated, so that the descent on the source site is
  available with no further hypothesis.
* `Stacks.SheafOfModules.ChangeOfRings.liftedSMul_sitePushforward`: **the computation the
  transport rests on** — the lifted action of a section of `S'` on a pushed-forward section is
  the lifted action of its image in `R'`.
* `SheafOfModules.GradedAlgebra.descendSitePushforwardHom_app_val_app`: the transport is the
  identity on local sections, and
  `SheafOfModules.GradedAlgebra.isIso_descendSitePushforwardHom_app`: it is an isomorphism in
  every degree.
* `SheafOfModules.GradedAlgebra.isExteriorAlgebra_descendSitePushforward`,
  `SheafOfModules.GradedAlgebra.isExteriorAlgebra_of_descendSitePushforward` and their slice
  forms `SheafOfModules.GradedAlgebra.isExteriorAlgebra_descendOver`,
  `SheafOfModules.GradedAlgebra.isExteriorAlgebra_of_descendOver`: **the universal property of
  an exterior algebra crosses the transport**, in either direction, on the image of the
  degree-one generator.
* `SheafOfModules.GradedAlgebra.over_eq_sitePushforward`: restriction of a sheaf of graded
  algebras to a slice site is its pushforward along `Over.forget U`, by definition.

## Implementation notes

**Every object in sight has the same underlying presheaf of abelian groups**, namely that of the
original algebra read at the images of the objects of the source site: `liftedSheaf` leaves the
presheaf untouched and so does `pushforward`, up to precomposition with `F.op`. So the transport
is the identity on sections and the only content is that the two `S'`-actions agree.

**That agreement is a separatedness argument and not a definitional unfolding.** On one side the
action of `a : S'(V)` is the action of `φ'(a) : R'(F V)` lifted through `α`; on the other it is
the action of `a` itself lifted through `β`. Both are amalgamations of local products, over the
image sieve of `a` under `β`; over a member of that sieve carrying a lift `b` of `a`, the square
makes `φ(b)` a lift of `φ'(a)`, and both sides restrict to the action of `φ(b)`. The pushforward
of a sheaf is a sheaf, hence separated, which concludes.

**The three algebra laws need no transport at all.** The multiplication and the unit of a
descended algebra are those of the original on sections
(`SheafOfModules.GradedAlgebra.descend_mul_app` and `descend_one_eval` are `rfl`), and so are
those of a pushforward (`SheafOfModules.GradedAlgebra.pushforward_mul_app` and
`pushforward_one_eval`). Both composites therefore carry the multiplication of the original
algebra read at `F V`, and multiplicativity and unitality of the transport are `rfl`.

## References

* [Stacks Project, Tag 08M3](https://stacks.math.columbia.edu/tag/08M3)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe v v' u u' t

namespace Stacks.SheafOfModules.ChangeOfRings

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  [F.IsContinuous J K]
  {S S' : Sheaf J RingCat.{t}} {R R' : Sheaf K RingCat.{t}}
  (α : R ⟶ R') [Presheaf.IsLocallySurjective K α.hom]
  (β : S ⟶ S') [Presheaf.IsLocallySurjective J β.hom]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{t} J K).obj R)
  (φ' : S' ⟶ (F.sheafPushforwardContinuous RingCat.{t} J K).obj R')
  (hsq : φ ≫ (F.sheafPushforwardContinuous RingCat.{t} J K).map α = β ≫ φ')

/-- The image under a structure map `ψ : T ⟶ F_* Q` of a section of `T`, with its result type
written as a section of `Q` over the image object rather than as a section of the pushforward.

The two types are definitionally equal, but a statement written in the pushforward spelling
carries the scalar action of the wrong ring, so the elaborator finds no `HSMul` instance. This
must be a `def` with an ascribed result type, as
`Stacks.SheafOfModules.ChangeOfRings.sectionRestrict` is for the same reason. -/
def pushScalar {T : Sheaf J RingCat.{t}} {Q : Sheaf K RingCat.{t}}
    (ψ : T ⟶ (F.sheafPushforwardContinuous RingCat.{t} J K).obj Q) (V : Cᵒᵖ)
    (b : T.obj.obj V) : Q.obj.obj (op (F.obj V.unop)) :=
  (ψ.hom.app V).hom b

/-- A structure map commutes with restriction along a morphism of the source site. -/
theorem pushScalar_naturality {T : Sheaf J RingCat.{t}} {Q : Sheaf K RingCat.{t}}
    (ψ : T ⟶ (F.sheafPushforwardContinuous RingCat.{t} J K).obj Q) {V : Cᵒᵖ} {W : C}
    (g : W ⟶ V.unop) (b : T.obj.obj V) :
    pushScalar ψ (op W) ((T.obj.map g.op).hom b) =
      (Q.obj.map (F.map g).op).hom (pushScalar ψ V b) :=
  ConcreteCategory.congr_hom (ψ.hom.naturality g.op) b

omit [Presheaf.IsLocallySurjective K α.hom] [Presheaf.IsLocallySurjective J β.hom] in
include hsq in
/-- The commuting square, on sections: the image under `α` of the image of a section of `S`
under `φ` is the image under `φ'` of its image under `β`. -/
theorem hom_app_sq (V : Cᵒᵖ) (b : S.obj.obj V) :
    (α.hom.app (op (F.obj V.unop))).hom (pushScalar φ V b) =
      pushScalar φ' V ((β.hom.app V).hom b) :=
  congrArg (fun ψ : S ⟶ (F.sheafPushforwardContinuous RingCat.{t} J K).obj R' =>
    (ψ.hom.app V).hom b) hsq

section Module

variable (G : SheafOfModules.{t} R)
  (hG : ∀ (X : Dᵒᵖ) (b : R.obj.obj X), b ∈ RingHom.ker (α.hom.app X).hom →
    ∀ m : G.val.obj X, b • m = 0)

omit [Presheaf.IsLocallySurjective K α.hom] [Presheaf.IsLocallySurjective J β.hom] in
include hsq hG in
/-- **The pushforward of an annihilated sheaf of modules is annihilated.** A section of `S` in
the kernel of `β` acts on the pushforward through `φ`, and the square puts its image under `φ`
in the kernel of `α`. -/
theorem smul_pushforward_eq_zero (V : Cᵒᵖ) (b : S.obj.obj V)
    (hb : b ∈ RingHom.ker (β.hom.app V).hom)
    (m : ((_root_.SheafOfModules.pushforward.{t} φ).obj G).val.obj V) : b • m = 0 := by
  refine hG (op (F.obj V.unop)) (pushScalar φ V b) ?_ m
  rw [RingHom.mem_ker, hom_app_sq α β φ φ' hsq V b, RingHom.mem_ker.1 hb]
  exact map_zero _

variable
  (hG' : ∀ (V : Cᵒᵖ) (b : S.obj.obj V), b ∈ RingHom.ker (β.hom.app V).hom →
    ∀ m : ((_root_.SheafOfModules.pushforward.{t} φ).obj G).val.obj V, b • m = 0)

include hsq in
/-- **The computation the transport rests on.** The action on a section of the pushforward of a
section `a` of `S'`, lifted through `β`, is the action of its image `φ'(a)` lifted through `α`.

Both sides are amalgamations of local products. Over a member of the image sieve of `a` under
`β` carrying a lift `b`, the commuting square makes `φ(b)` a lift of `φ'(a)`, and both sides
restrict there to the action of `φ(b)`; the pushforward of a sheaf is separated. -/
theorem liftedSMul_sitePushforward (V : Cᵒᵖ) (a : S'.obj.obj V)
    (m : ((_root_.SheafOfModules.pushforward.{t} φ).obj G).val.obj V) :
    liftedSMul α G hG (pushScalar φ' V a) m =
      liftedSMul β ((_root_.SheafOfModules.pushforward.{t} φ).obj G) hG' a m := by
  refine sections_ext ((_root_.SheafOfModules.pushforward.{t} φ).obj G)
    (Presheaf.imageSieve_mem J β.hom a) (fun W g hg => ?_)
  obtain ⟨b, hb⟩ := hg
  have hlift : (α.hom.app (op (F.obj W))).hom (pushScalar φ (op W) b) =
      (R'.obj.map (F.map g).op).hom (pushScalar φ' V a) := by
    rw [hom_app_sq α β φ φ' hsq (op W) b, hb]
    exact pushScalar_naturality φ' g a
  exact (map_liftedSMul α G hG (pushScalar φ' V a) m (F.map g) _ hlift).trans
    (map_liftedSMul β ((_root_.SheafOfModules.pushforward.{t} φ).obj G) hG' a m g b hb).symm

/-- The identity of the common underlying presheaf of abelian groups, read as a morphism from
the pushforward of the descended sheaf to the descent of the pushforward. -/
def sitePushforwardLiftedPresheafId :
    ((_root_.SheafOfModules.pushforward.{t} φ').obj (liftedSheaf α G hG)).val.presheaf ⟶
      (liftedSheaf β ((_root_.SheafOfModules.pushforward.{t} φ).obj G) hG').val.presheaf :=
  𝟙 _

include hsq in
/-- **The module-level transport.** The pushforward along `φ'` of the descent along `α` of an
annihilated sheaf of `R`-modules is the descent along `β` of its pushforward along `φ`: the same
presheaf of abelian groups, with the same `S'`-action. -/
def liftedSheafSitePushforwardIso :
    (_root_.SheafOfModules.pushforward.{t} φ').obj (liftedSheaf α G hG) ≅
      liftedSheaf β ((_root_.SheafOfModules.pushforward.{t} φ).obj G) hG' where
  hom := ⟨PresheafOfModules.homMk (sitePushforwardLiftedPresheafId α β φ φ' G hG hG')
    (fun V a m => liftedSMul_sitePushforward α β φ φ' hsq G hG hG' V a m)⟩
  inv := ⟨PresheafOfModules.homMk
    (M₂ := ((_root_.SheafOfModules.pushforward.{t} φ').obj (liftedSheaf α G hG)).val)
    (sitePushforwardLiftedPresheafId α β φ φ' G hG hG')
    (fun V a m => (liftedSMul_sitePushforward α β φ φ' hsq G hG hG' V a m).symm)⟩
  hom_inv_id := by ext; rfl
  inv_hom_id := by ext; rfl

/-- The isomorphism `liftedSheafSitePushforwardIso` is the identity on local sections. -/
@[simp]
theorem liftedSheafSitePushforwardIso_hom_val_app (V : Cᵒᵖ)
    (m : ((_root_.SheafOfModules.pushforward.{t} φ').obj (liftedSheaf α G hG)).val.obj V) :
    (liftedSheafSitePushforwardIso α β φ φ' hsq G hG hG').hom.val.app V m = m :=
  rfl

end Module

end Stacks.SheafOfModules.ChangeOfRings

namespace SheafOfModules.GradedAlgebra

open Stacks.SheafOfModules.ChangeOfRings

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  [F.IsContinuous J K]
  {S S' : Sheaf J RingCat.{t}} {R R' : Sheaf K RingCat.{t}}
  (α : R ⟶ R') [Presheaf.IsLocallySurjective K α.hom]
  (β : S ⟶ S') [Presheaf.IsLocallySurjective J β.hom]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{t} J K).obj R)
  (φ' : S' ⟶ (F.sheafPushforwardContinuous RingCat.{t} J K).obj R')
  (hsq : φ ≫ (F.sheafPushforwardContinuous RingCat.{t} J K).map α = β ≫ φ')
  (A : GradedAlgebra.{t, t} R)
  (hA : ∀ (n : ℤ) (X : Dᵒᵖ) (b : R.obj.obj X), b ∈ RingHom.ker (α.hom.app X).hom →
    ∀ m : (A.piece n).val.obj X, b • m = 0)
  (hA' : ∀ (n : ℤ) (V : Cᵒᵖ) (b : S.obj.obj V), b ∈ RingHom.ker (β.hom.app V).hom →
    ∀ m : ((pushforward φ A).piece n).val.obj V, b • m = 0)

include hsq in
/-- **Descent commutes with pushforward along a continuous functor of sites.** Pushing the
descended algebra forward along `φ'` and descending the pushed-forward algebra along `β` give
the same sheaf of graded `S'`-algebras, identified here by a unital homomorphism which is the
identity on local sections.

The two algebras have the same pieces by
`Stacks.SheafOfModules.ChangeOfRings.liftedSheafSitePushforwardIso`, and the multiplication and
the unit of each are those of `A` read at the images of the objects of the source site, so the
two laws are `rfl`. -/
def descendSitePushforwardHom :
    UnitalHom (pushforward φ' (descend α A hA)) (descend β (pushforward φ A) hA') where
  app n := (liftedSheafSitePushforwardIso α β φ φ' hsq (A.piece n) (hA n) (hA' n)).hom
  map_mul _ _ _ _ _ := rfl
  map_one _ := rfl

include hsq in
/-- The transport is the identity on local sections. -/
theorem descendSitePushforwardHom_app_val_app (n : ℤ) (V : Cᵒᵖ)
    (x : ((pushforward φ' (descend α A hA)).piece n).val.obj V) :
    ((descendSitePushforwardHom α β φ φ' hsq A hA hA').app n).val.app V x = x :=
  rfl

include hsq in
/-- **Every degree of the transport is an isomorphism.** -/
instance isIso_descendSitePushforwardHom_app (n : ℤ) :
    IsIso ((descendSitePushforwardHom α β φ φ' hsq A hA hA').app n) :=
  (liftedSheafSitePushforwardIso α β φ φ' hsq (A.piece n) (hA n) (hA' n)).isIso_hom

include hsq in
/-- **The transport, as an isomorphism of sheaves of graded `S'`-algebras.** -/
def descendSitePushforwardIso :
    pushforward φ' (descend α A hA) ≅ descend β (pushforward φ A) hA' where
  hom := (descendSitePushforwardHom α β φ φ' hsq A hA hA').toHom
  inv := (descendSitePushforwardHom α β φ φ' hsq A hA hA').inverse.toHom
  hom_inv_id := by
    refine Hom.ext fun n => ?_
    simpa using IsIso.hom_inv_id ((descendSitePushforwardHom α β φ φ' hsq A hA hA').app n)
  inv_hom_id := by
    refine Hom.ext fun n => ?_
    simpa using IsIso.inv_hom_id ((descendSitePushforwardHom α β φ φ' hsq A hA hA').app n)

include hsq in
/-- **The universal property of an exterior algebra crosses the interchange.** If the
pushforward of the descended algebra is an exterior algebra on a degree-one generator, then so
is the descent of the pushforward, on the image of that generator under the transport: the two
presentations of the same algebra are degreewise isomorphic, and a universal property transports
along a degreewise isomorphism. -/
theorem isExteriorAlgebra_descendSitePushforward {M : _root_.SheafOfModules.{t} S'}
    {ι : M ⟶ (pushforward φ' (descend α A hA)).piece 1}
    (h : IsExteriorAlgebra (pushforward φ' (descend α A hA)) ι) :
    IsExteriorAlgebra (descend β (pushforward φ A) hA')
      (ι ≫ (descendSitePushforwardHom α β φ φ' hsq A hA hA').app 1) :=
  h.isUniversal.ofDegreewiseIso _
    (h.1.compUnitalHom (descendSitePushforwardHom α β φ φ' hsq A hA hA'))

include hsq in
/-- **The universal property of an exterior algebra crosses the interchange backwards.** The
converse direction of `SheafOfModules.GradedAlgebra.isExteriorAlgebra_descendSitePushforward`,
along the degreewise inverse of the transport. -/
theorem isExteriorAlgebra_of_descendSitePushforward
    {M : _root_.SheafOfModules.{t} S'}
    {ι : M ⟶ (descend β (pushforward φ A) hA').piece 1}
    (h : IsExteriorAlgebra (descend β (pushforward φ A) hA') ι) :
    IsExteriorAlgebra (pushforward φ' (descend α A hA))
      (ι ≫ (descendSitePushforwardHom α β φ φ' hsq A hA hA').inverse.app 1) := by
  have : ∀ n, IsIso ((descendSitePushforwardHom α β φ φ' hsq A hA hA').inverse.app n) :=
    fun n => inferInstanceAs
      (IsIso (inv ((descendSitePushforwardHom α β φ φ' hsq A hA hA').app n)))
  exact h.isUniversal.ofDegreewiseIso _
    (h.1.compUnitalHom (descendSitePushforwardHom α β φ φ' hsq A hA hA').inverse)

end SheafOfModules.GradedAlgebra

namespace SheafOfModules.GradedAlgebra

open Stacks.SheafOfModules.ChangeOfRings

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R R' : Sheaf J RingCat.{t}} (α : R ⟶ R') [Presheaf.IsLocallySurjective J α.hom] (U : C)

/-- The restriction of a morphism of sheaves of rings to the slice site at `U`. -/
abbrev overRingHom : R.over U ⟶ R'.over U :=
  (J.overPullback RingCat.{t} U).map α

/-- The restriction of a locally surjective morphism of sheaves of rings to the slice site at `U`
is locally surjective. -/
instance isLocallySurjective_overRingHom :
    Presheaf.IsLocallySurjective (J.over U) (overRingHom α U).hom :=
  Presheaf.isLocallySurjective_whisker (J.over U) J (Over.forget U) α.hom

/-- Restriction of a sheaf of graded algebras to the slice site at `U` is its pushforward along
`Over.forget U`, the structure map being the identity: the two spellings of the restricted
algebra are the same object. -/
theorem over_eq_sitePushforward (A : GradedAlgebra.{t, t} R) :
    A.over U = pushforward (G := Over.forget U) (𝟙 (R.over U)) A :=
  rfl

variable (A : GradedAlgebra.{t, t} R)
  (hA : ∀ (n : ℤ) (X : Cᵒᵖ) (b : R.obj.obj X), b ∈ RingHom.ker (α.hom.app X).hom →
    ∀ m : (A.piece n).val.obj X, b • m = 0)
  (hA' : ∀ (n : ℤ) (V : (Over U)ᵒᵖ) (b : (R.over U).obj.obj V),
    b ∈ RingHom.ker ((overRingHom α U).hom.app V).hom →
    ∀ m : ((A.over U).piece n).val.obj V, b • m = 0)

/-- **Descent commutes with restriction to a slice site**, the case `F = Over.forget U` of
`SheafOfModules.GradedAlgebra.descendSitePushforwardHom`: the restriction to the slice site at
`U` of an algebra descended along `α` is the descent along the restriction of `α` of the
restricted algebra. -/
def descendOverHom :
    UnitalHom ((descend α A hA).over U) (descend (overRingHom α U) (A.over U) hA') :=
  descendSitePushforwardHom (F := Over.forget U) α (overRingHom α U) (𝟙 (R.over U))
    (𝟙 (R'.over U)) (by rw [Category.id_comp, Category.comp_id]) A hA hA'

/-- The restricted transport is the identity on local sections. -/
theorem descendOverHom_app_val_app (n : ℤ) (V : (Over U)ᵒᵖ)
    (x : (((descend α A hA).over U).piece n).val.obj V) :
    ((descendOverHom α U A hA hA').app n).val.app V x = x :=
  rfl

/-- **Every degree of the restricted transport is an isomorphism.** -/
instance isIso_descendOverHom_app (n : ℤ) : IsIso ((descendOverHom α U A hA hA').app n) :=
  isIso_descendSitePushforwardHom_app (F := Over.forget U) α (overRingHom α U) (𝟙 (R.over U))
    (𝟙 (R'.over U)) (by rw [Category.id_comp, Category.comp_id]) A hA hA' n

/-- **The restricted transport, as an isomorphism of sheaves of graded algebras.** -/
def descendOverIso :
    (descend α A hA).over U ≅ descend (overRingHom α U) (A.over U) hA' :=
  descendSitePushforwardIso (F := Over.forget U) α (overRingHom α U) (𝟙 (R.over U))
    (𝟙 (R'.over U)) (by rw [Category.id_comp, Category.comp_id]) A hA hA'

/-- **The universal property of an exterior algebra crosses the restriction to a slice site**,
for a descended algebra. -/
theorem isExteriorAlgebra_descendOver {M : _root_.SheafOfModules.{t} (R'.over U)}
    {ι : M ⟶ ((descend α A hA).over U).piece 1}
    (h : IsExteriorAlgebra ((descend α A hA).over U) ι) :
    IsExteriorAlgebra (descend (overRingHom α U) (A.over U) hA')
      (ι ≫ (descendOverHom α U A hA hA').app 1) :=
  isExteriorAlgebra_descendSitePushforward (F := Over.forget U) α (overRingHom α U)
    (𝟙 (R.over U)) (𝟙 (R'.over U)) (by rw [Category.id_comp, Category.comp_id]) A hA hA' h

/-- **The universal property of an exterior algebra crosses the restriction to a slice site
backwards**, for a descended algebra: the universal property for the descent of the restriction
gives it for the restriction of the descent. -/
theorem isExteriorAlgebra_of_descendOver {M : _root_.SheafOfModules.{t} (R'.over U)}
    {ι : M ⟶ (descend (overRingHom α U) (A.over U) hA').piece 1}
    (h : IsExteriorAlgebra (descend (overRingHom α U) (A.over U) hA') ι) :
    IsExteriorAlgebra ((descend α A hA).over U)
      (ι ≫ (descendOverHom α U A hA hA').inverse.app 1) :=
  isExteriorAlgebra_of_descendSitePushforward (F := Over.forget U) α (overRingHom α U)
    (𝟙 (R.over U)) (𝟙 (R'.over U)) (by rw [Category.id_comp, Category.comp_id]) A hA hA' h

end SheafOfModules.GradedAlgebra

end
