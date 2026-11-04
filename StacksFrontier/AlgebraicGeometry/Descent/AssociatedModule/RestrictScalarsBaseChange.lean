module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianRestriction
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleHomSheafGlue
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRingedSite

/-!
# The base-change comparison after restriction of scalars along an isomorphism

Let `ψ : R ⟶ R'` be an isomorphism of presheaves of commutative rings on a category `C` and let
`M` be a presheaf of modules over `R'`.  Restricting the scalars of `M` along `ψ` changes neither
the sections nor the restriction maps, only the rings acting on them.  Consequently the
base-change comparison

`R Y ⊗[R X] M X ⟶ M Y`

of the restriction map of `M` along `f : X ⟶ Y` is carried to the comparison
`R' Y ⊗[R' X] M X ⟶ M Y` by the transport of the tensor product along `ψ`, and the two are
bijective together.  Being cartesian over `f`, i.e. clause (1) of the characterization of
quasi-coherence of Stacks 0H04, therefore does not see restriction of scalars along an
isomorphism.

The transport of the tensor product is isolated as `Stacks.RingSquare.tensorMap`: for a
commuting square of ring maps

`A → A'`, `B → B'`, `α : A ≃ B`, `β : A' ≃ B'`

and a `B`-module `P`, viewed as an `A`-module through `α`, it is the additive map
`A' ⊗[A] P ⟶ B' ⊗[B] P` sending `c ⊗ₜ x` to `β c ⊗ₜ x`.

The application is to the small étale site of a scheme `S`, whose associated-module adjunction
has as right adjoint `AlgebraicGeometry.SmallEtale.restrictModule`, the pushforward along
`AlgebraicGeometry.SmallEtale.structureMap`.  That structure map is not the identity: its
component at an open `U` is the identification `Γ(S, U) ≅ Γ(U, ⊤)` of the sections of `𝒪_S` over
`U` with the global functions of the open subscheme `U`.  It is nevertheless an isomorphism, so
the sections of a restricted sheaf of modules are cartesian over an inclusion `V' ≤ V` of opens
of `S` as soon as they are cartesian over the corresponding morphism of the small étale site;
this is the scalar bookkeeping in clause (2) of Stacks 03DX at `τ = étale`.

## Main definitions

* `Stacks.RingSquare.tensorMap`: the transport of a tensor product along a commuting square of
  ring maps with isomorphisms for vertical maps.
* `AlgebraicGeometry.SmallEtale.commStructureMap`: the structure map of the small étale site of a
  scheme, valued in commutative rings.

## Main results

* `Stacks.RingSquare.bijective_tensorMap`: the transport of a tensor product along such a square
  is bijective.
* `Stacks.PresheafOfModules.bijective_restrictionBaseChange_restrictScalars`: restriction of
  scalars along an isomorphism of presheaves of commutative rings preserves bijectivity of the
  base-change comparison of a restriction map.
* `AlgebraicGeometry.SmallEtale.bijective_restrictionBaseChange_restrictModule`: the same
  statement for the restriction of a sheaf of modules on the small étale site of a scheme to the
  small Zariski site.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0H04](https://stacks.math.columbia.edu/tag/0H04)
-/

@[expose] public section

open CategoryTheory

open scoped ChangeOfRings

universe u v r m w

namespace Stacks.RingSquare

section

variable {A A' B B' : Type*} {P : Type w}
  [CommRing A] [CommRing A'] [CommRing B] [CommRing B'] [AddCommGroup P]
  [Module A A'] [Module B B'] [Module A P] [Module B P]
  (a : A →+* A') (b : B →+* B') (α : A ≃+* B) (β : A' ≃+* B')

/-- Transport of a tensor product along a commuting square of ring maps whose vertical maps `α`
and `β` are isomorphisms: the additive map `A' ⊗[A] P ⟶ B' ⊗[B] P` sending `c ⊗ₜ x` to
`β c ⊗ₜ x`.  The hypotheses `hA`, `hB` and `hP` say that the three module structures in play are
the ones obtained from `a`, `b` and `α` by restriction of scalars. -/
def tensorMap (hsq : ∀ t, β (a t) = b (α t))
    (hA : ∀ (t : A) (c : A'), t • c = a t * c)
    (hB : ∀ (s : B) (d : B'), s • d = b s * d)
    (hP : ∀ (t : A) (x : P), t • x = α t • x) :
    TensorProduct A A' P →+ TensorProduct B B' P :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk'
      (fun c => AddMonoidHom.mk' (fun x => (β c) ⊗ₜ[B] x)
        (fun x y => TensorProduct.tmul_add _ _ _))
      (fun c d => AddMonoidHom.ext fun x => by
        change (β (c + d)) ⊗ₜ[B] x = (β c) ⊗ₜ[B] x + (β d) ⊗ₜ[B] x
        rw [map_add, TensorProduct.add_tmul]))
    (fun t c x => by
      change (β (t • c)) ⊗ₜ[B] x = (β c) ⊗ₜ[B] (t • x)
      rw [hA, map_mul, hsq, ← hB, TensorProduct.smul_tmul, hP])

/-- `Stacks.RingSquare.tensorMap` on a pure tensor. -/
@[simp]
theorem tensorMap_tmul (hsq hA hB hP) (c : A') (x : P) :
    tensorMap a b α β hsq hA hB hP (c ⊗ₜ[A] x) = (β c) ⊗ₜ[B] x := rfl

/-- **The transport of a tensor product along a square of ring maps with invertible vertical maps
is bijective.**  The inverse is the transport along the inverse square. -/
theorem bijective_tensorMap (hsq : ∀ t, β (a t) = b (α t))
    (hA : ∀ (t : A) (c : A'), t • c = a t * c)
    (hB : ∀ (s : B) (d : B'), s • d = b s * d)
    (hP : ∀ (t : A) (x : P), t • x = α t • x) :
    Function.Bijective (tensorMap a b α β hsq hA hB hP) := by
  have hsq' : ∀ s, β.symm (b s) = a (α.symm s) := fun s => by
    conv_lhs => rw [← α.apply_symm_apply s, ← hsq]
    rw [β.symm_apply_apply]
  have hP' : ∀ (s : B) (x : P), s • x = α.symm s • x := fun s x => by
    rw [hP, α.apply_symm_apply]
  refine Function.bijective_iff_has_inverse.mpr
    ⟨tensorMap b a α.symm β.symm hsq' hB hA hP', fun z => ?_, fun z => ?_⟩
  · induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul c x => simp
    | add z w hz hw => rw [map_add, map_add, hz, hw]
  · induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul d x => simp
    | add z w hz hw => rw [map_add, map_add, hz, hw]

end

end Stacks.RingSquare

namespace Stacks.PresheafOfModules

variable {C : Type u} [Category.{v} C] {R R' : Cᵒᵖ ⥤ CommRingCat.{r}}

/-- **Restriction of scalars along an isomorphism of presheaves of commutative rings preserves
bijectivity of the base-change comparison.**  The sections and the restriction maps of the
restricted presheaf of modules are those of the original one, so the two comparisons agree up to
the transport `Stacks.RingSquare.tensorMap` of the tensor product along `ψ`. -/
theorem bijective_restrictionBaseChange_restrictScalars (ψ : R ⟶ R')
    (hψ : ∀ Z, IsIso (ψ.app Z))
    (M : PresheafOfModules.{max m r} (R' ⋙ forget₂ CommRingCat RingCat))
    {X Y : Cᵒᵖ} (g : X ⟶ Y)
    (h : Function.Bijective (restrictionBaseChange (R := R') M g)) :
    Function.Bijective (restrictionBaseChange (R := R)
      ((_root_.PresheafOfModules.restrictScalars
        (Functor.whiskerRight ψ (forget₂ CommRingCat RingCat))).obj M) g) := by
  have _ : IsIso (ψ.app X) := hψ X
  have _ : IsIso (ψ.app Y) := hψ Y
  set NM := (_root_.PresheafOfModules.restrictScalars
    (Functor.whiskerRight ψ (forget₂ CommRingCat RingCat))).obj M
  let _ : Module (R.obj X) (R.obj Y) := Module.compHom _ (R.map g).hom
  let _ : Module (R'.obj X) (R'.obj Y) := Module.compHom _ (R'.map g).hom
  let _ : Module (R.obj X) (M.obj X) := Module.compHom _ (ψ.app X).hom
  let u := Stacks.RingSquare.tensorMap (P := M.obj X) (R.map g).hom (R'.map g).hom
    (asIso (ψ.app X)).commRingCatIsoToRingEquiv (asIso (ψ.app Y)).commRingCatIsoToRingEquiv
    (fun t => RingHom.congr_fun (congrArg CommRingCat.Hom.hom (ψ.naturality g)) t)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
  have hu : Function.Bijective u := Stacks.RingSquare.bijective_tensorMap _ _ _ _ _ _ _ _
  have hcomp : ∀ z, (restrictionBaseChange (R := R') M g).hom (u z)
      = (restrictionBaseChange (R := R) NM g).hom z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero =>
      refine Eq.trans (congrArg _ (map_zero u)) ?_
      exact (map_zero (restrictionBaseChange (R := R') M g).hom).trans
        (map_zero (restrictionBaseChange (R := R) NM g).hom).symm
    | tmul c x =>
      exact (restrictionBaseChange_tmul M g ((ψ.app Y).hom c) x).trans
        (restrictionBaseChange_tmul NM g c x).symm
    | add z w hz hw =>
      refine Eq.trans (congrArg _ (map_add u z w)) ?_
      refine Eq.trans (map_add (restrictionBaseChange (R := R') M g).hom _ _) ?_
      exact (congrArg₂ (· + ·) hz hw).trans
        (map_add (restrictionBaseChange (R := R) NM g).hom z w).symm
  have hfun : (⇑(restrictionBaseChange (R := R) NM g).hom)
      = (⇑(restrictionBaseChange (R := R') M g).hom) ∘ (⇑u) := funext fun z => (hcomp z).symm
  rw [show (⇑(ConcreteCategory.hom (restrictionBaseChange (R := R) NM g))) = _ from hfun]
  exact h.comp hu

end Stacks.PresheafOfModules

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The comparison of structure sheaves along the inclusion of the small Zariski site of `S` into
the small étale site of `S`, valued in commutative rings: over an open `U` it is the
identification of the sections of `𝒪_S` over `U` with the global functions of the open subscheme
`U`.  Forgetting commutativity gives `AlgebraicGeometry.SmallEtale.structureMap`. -/
noncomputable def commStructureMap :
    S.presheaf ⟶ (opensToSmallEtale B S hS).op ⋙ commStructurePresheaf B S hS where
  app U := (Scheme.Opens.topIso U.unop).inv
  naturality _ _ h := (Scheme.Opens.topIso_inv_appTop (X := S) (leOfHom h.unop)).symm

/-- **Cartesian sections descend from the small étale site to the small Zariski site.**  If the
sections of a sheaf of modules on the small étale site of `S` are the base change of one another
along the morphism of the site attached to an inclusion `V' ≤ V` of opens of `S`, then the same
holds for its restriction along the structure map, since that map is an isomorphism of presheaves
of rings. -/
theorem bijective_restrictionBaseChange_restrictModule
    (G : SheafOfModules.{u} (structureSheaf B S hS))
    {V V' : S.Opens} (hle : V' ≤ V)
    (h : Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange
      (R := commStructurePresheaf B S hS) G.val
      ((opensToSmallEtale B S hS).map (homOfLE hle)).op)) :
    Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange
      (R := S.presheaf) ((restrictModule B S hS).obj G).val (homOfLE hle).op) :=
  Stacks.PresheafOfModules.bijective_restrictionBaseChange_restrictScalars
    (commStructureMap B S hS)
    (fun U => inferInstanceAs (IsIso (Scheme.Opens.topIso U.unop).inv))
    ((PresheafOfModules.pushforward₀ (opensToSmallEtale B S hS)
      (commStructurePresheaf B S hS ⋙ forget₂ CommRingCat RingCat)).obj G.val)
    (homOfLE hle).op h

end AlgebraicGeometry.SmallEtale

end
