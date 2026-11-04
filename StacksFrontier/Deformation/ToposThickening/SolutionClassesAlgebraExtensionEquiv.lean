module

public import StacksFrontier.Deformation.ToposThickening.KernelPushoutAlgebraExtension

/-!
# Isomorphism classes of solutions through an equivalence of categories of algebra extensions

The solutions of a square-zero extension problem `S` of [Stacks Project, Tag 08UF] are the
extensions `0 → 𝒢 → 𝒪' → 𝒪 → 0` of `𝒜`-algebras inducing the prescribed map `c` on the base ideal
(`Deformation.ToposThickening.RingedToposExtensionProblem.IsCompatible`), for any `𝒜` identified
with the inverse image of the thickened base. This file records two facts about that condition
and the resulting comparison of isomorphism classes.

* Compatibility is invariant under morphisms of extensions, and it is enough to check it on the
  objects in the essential image of an essentially surjective functor into the site.
* If an equivalence of categories `R` carries the extensions of `S` to those of a second problem
  `S'` and preserves and reflects compatibility, then `R` induces a bijection between the
  isomorphism classes of solutions of `S` and of `S'`.

## Main definitions

* `Deformation.ToposThickening.RingedToposExtensionProblem.transportSolution`: the solution of
  `S'` attached to a solution of `S` by `R`.
* `isomorphismClassesEquivOfAlgebraExtension` (in
  `Deformation.ToposThickening.RingedToposExtensionProblem`): the bijection of isomorphism classes.
* `Deformation.ToposThickening.RingedToposExtensionProblem.addTorsorTransfer`: a torsor
  transported along a bijection and an isomorphism of groups.

## Main results

* `Deformation.ToposThickening.RingedToposExtensionProblem.isCompatible_of_hom`: compatibility
  is carried along morphisms of extensions.
* `Deformation.ToposThickening.RingedToposExtensionProblem.isCompatible_of_essSurj`:
  compatibility on the essential image of an essentially surjective functor is compatibility.

## References

* [Stacks Project, Tag 08UF](https://stacks.math.columbia.edu/tag/08UF)
* [Stacks Project, Tag 0D17](https://stacks.math.columbia.edu/tag/0D17)
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)

universe v u w v' u' w' v₂ u₂ v₃ u₃

namespace Deformation.ToposThickening.RingedToposExtensionProblem

open CompatibleFirstOrderThickening AlgebraExtension

section Compatible

variable {X : RingedTopos.{v, u, w}} {B : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [B.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  (S : RingedToposExtensionProblem X B)
  {A : Sheaf X.J CommRingCat.{w}} {a : A ⟶ X.O}
  (θ : A ≅ (inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension)
  {M : SheafOfModules.{w} ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj X.O)}
  {c : S.I ⟶ (SheafOfModules.restrictScalars
    ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).map S.f.fSharpInverseImage)).obj M}

/-- **Compatibility is carried along morphisms of extensions** of `𝒜`-algebras by `ℳ`. -/
theorem isCompatible_of_hom {Q Q' : AlgebraExtension a M} (g : Q ⟶ Q')
    (h : S.IsCompatible θ c Q) : S.IsCompatible θ c Q' := fun U x => by
  change Q'.algebraMap.hom.app U _ = _
  rw [← MapAlong.algebraMap_apply g]
  change g.hom.hom.app U (S.idealImage θ Q x) = _
  rw [h U x]
  exact g.kernel_comm U _

/-- **Compatibility can be checked on the essential image of an essentially surjective functor**
`G : 𝒟 ⥤ 𝒞` into the site. -/
theorem isCompatible_of_essSurj {D : Type u₂} [Category.{v₂} D] (G : D ⥤ X.C) [G.EssSurj]
    (Q : AlgebraExtension a M)
    (h : ∀ (V : Dᵒᵖ) (x : S.I.val.obj (G.op.obj V)),
      S.idealImage θ Q x = Q.incl (show M.val.obj (G.op.obj V) from c.val.app _ x)) :
    S.IsCompatible θ c Q := fun U x => by
  let i : U ≅ G.op.obj (Opposite.op (G.objPreimage U.unop)) := (G.objObjPreimageIso U.unop).op
  have hx : S.I.val.map i.inv (S.I.val.map i.hom x) = x := by
    rw [← PresheafOfModules.map_comp_apply, i.hom_inv_id, PresheafOfModules.map_id]
    rfl
  have h3 := PresheafOfModules.naturality_apply c.val i.inv (S.I.val.map i.hom x)
  calc S.idealImage θ Q x
      = S.idealImage θ Q (U := U) (S.I.val.map i.inv (S.I.val.map i.hom x)) := by
        rw [hx]
    _ = Q.extension.obj.map i.inv (S.idealImage θ Q (S.I.val.map i.hom x)) :=
        S.idealImage_naturality θ Q i.inv _
    _ = Q.extension.obj.map i.inv
          (Q.incl (U := G.op.obj _) (c.val.app _ (S.I.val.map i.hom x))) := by
        rw [h _ (S.I.val.map i.hom x)]
    _ = Q.incl (U := U) (M.val.map i.inv (c.val.app _ (S.I.val.map i.hom x))) :=
        (Q.incl_naturality i.inv _).symm
    _ = Q.incl (U := U) (c.val.app U (S.I.val.map i.inv (S.I.val.map i.hom x))) :=
        congrArg Q.incl h3.symm
    _ = Q.incl (U := U) (c.val.app U x) := by rw [hx]

end Compatible

/-! ### The bijection of isomorphism classes -/

section Transport

variable {X : RingedTopos.{v, u, w}} {X' : RingedTopos.{v₂, u₂, w}} {B : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [X'.J.HasSheafCompose (forget RingCat.{w})]
  [B.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget CommRingCat.{w})] [X'.J.HasSheafCompose (forget CommRingCat.{w})]
  (S : RingedToposExtensionProblem X B) (S' : RingedToposExtensionProblem X' B)
  {A : Sheaf X.J CommRingCat.{w}} {a : A ⟶ X.O}
  (θ : A ≅ (inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension)
  (hθ : θ.hom ≫ (inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction ≫
      S.f.fSharpInverseImage = a)
  {A' : Sheaf X'.J CommRingCat.{w}} {a' : A' ⟶ X'.O}
  (θ' : A' ≅ (inverseImageCommRingFunctor S'.f.toToposHom).obj S'.baseExtension)
  (hθ' : θ'.hom ≫ (inverseImageCommRingFunctor S'.f.toToposHom).map S'.baseReduction ≫
      S'.f.fSharpInverseImage = a')

/-- Two solutions are isomorphic exactly when they are isomorphic as extensions of
`𝒜`-algebras. -/
theorem isomorphic_iff_nonempty_iso_toAlgebraExtension (P Q : S.CompatibleFirstOrderThickening) :
    Isomorphic P Q ↔
      Nonempty ((S.toAlgebraExtensionFunctor θ hθ).obj P ≅
        (S.toAlgebraExtensionFunctor θ hθ).obj Q) :=
  ⟨fun ⟨e⟩ => ⟨(S.toAlgebraExtensionFunctor θ hθ).mapIso (show P ≅ Q from asIso e)⟩,
    fun ⟨e⟩ => ⟨((S.toAlgebraExtensionFullyFaithful θ hθ).preimageIso e).hom⟩⟩

variable (R : AlgebraExtension a S.G ⥤ AlgebraExtension a' S'.G)
  (hR : ∀ Q : AlgebraExtension a S.G, S.IsCompatible θ S.c Q ↔ S'.IsCompatible θ' S'.c (R.obj Q))

/-- **The solution of `S'` attached to a solution of `S`**: read the solution as an extension of
`𝒜`-algebras, apply `R`, and read the result back as a solution of `S'`. -/
abbrev transportSolution (P : S.CompatibleFirstOrderThickening) :
    S'.CompatibleFirstOrderThickening :=
  S'.ofAlgebraExtension θ' hθ' (R.obj ((S.toAlgebraExtensionFunctor θ hθ).obj P))
    ((hR _).1 (S.isCompatible_toAlgebraExtension θ hθ P))

/-- The extension of the transported solution is `R` of the extension of the solution. -/
def toAlgebraExtensionTransportSolutionIso (P : S.CompatibleFirstOrderThickening) :
    (S'.toAlgebraExtensionFunctor θ' hθ').obj (transportSolution S S' θ hθ θ' hθ' R hR P) ≅
      R.obj ((S.toAlgebraExtensionFunctor θ hθ).obj P) :=
  S'.toAlgebraExtensionOfAlgebraExtensionIso θ' hθ' _ _

variable [R.IsEquivalence]

/-- Two solutions of `S` are isomorphic exactly when their transports are. -/
theorem isomorphic_transportSolution_iff (P Q : S.CompatibleFirstOrderThickening) :
    Isomorphic (transportSolution S S' θ hθ θ' hθ' R hR P)
        (transportSolution S S' θ hθ θ' hθ' R hR Q) ↔ Isomorphic P Q := by
  rw [isomorphic_iff_nonempty_iso_toAlgebraExtension S' θ' hθ',
    isomorphic_iff_nonempty_iso_toAlgebraExtension S θ hθ]
  refine ⟨fun ⟨e⟩ => ⟨(Functor.FullyFaithful.ofFullyFaithful R).preimageIso
      ((toAlgebraExtensionTransportSolutionIso S S' θ hθ θ' hθ' R hR P).symm ≪≫ e ≪≫
        toAlgebraExtensionTransportSolutionIso S S' θ hθ θ' hθ' R hR Q)⟩,
    fun ⟨e⟩ => ⟨toAlgebraExtensionTransportSolutionIso S S' θ hθ θ' hθ' R hR P ≪≫ R.mapIso e ≪≫
      (toAlgebraExtensionTransportSolutionIso S S' θ hθ θ' hθ' R hR Q).symm⟩⟩

/-- Every solution of `S'` is isomorphic to the transport of a solution of `S`. -/
theorem exists_isomorphic_transportSolution (P' : S'.CompatibleFirstOrderThickening) :
    ∃ P : S.CompatibleFirstOrderThickening,
      Isomorphic (transportSolution S S' θ hθ θ' hθ' R hR P) P' := by
  let E' := (S'.toAlgebraExtensionFunctor θ' hθ').obj P'
  let i : R.obj (R.objPreimage E') ≅ E' := R.objObjPreimageIso E'
  have hQ : S.IsCompatible θ S.c (R.objPreimage E') :=
    (hR _).2 (S'.isCompatible_of_hom θ' i.inv (S'.isCompatible_toAlgebraExtension θ' hθ' P'))
  refine ⟨S.ofAlgebraExtension θ hθ (R.objPreimage E') hQ, ?_⟩
  rw [isomorphic_iff_nonempty_iso_toAlgebraExtension S' θ' hθ']
  exact ⟨toAlgebraExtensionTransportSolutionIso S S' θ hθ θ' hθ' R hR _ ≪≫
    R.mapIso (S.toAlgebraExtensionOfAlgebraExtensionIso θ hθ _ hQ) ≪≫ i⟩

/-- **The bijection of isomorphism classes of solutions induced by `R`**: the class of a solution
of `S` goes to the class of its transport. -/
def isomorphismClassesEquivOfAlgebraExtension : IsomorphismClasses S ≃ IsomorphismClasses S' :=
  Equiv.ofBijective
    (Quotient.map (transportSolution S S' θ hθ θ' hθ' R hR)
      (fun P Q h => (isomorphic_transportSolution_iff S S' θ hθ θ' hθ' R hR P Q).2 h))
    ⟨fun p q => Quotient.inductionOn₂ p q fun P Q h =>
        Quotient.sound ((isomorphic_transportSolution_iff S S' θ hθ θ' hθ' R hR P Q).1
          (Quotient.exact h)),
      fun p' => Quotient.inductionOn p' fun P' =>
        (exists_isomorphic_transportSolution S S' θ hθ θ' hθ' R hR P').elim fun P hP =>
          ⟨Quotient.mk _ P, Quotient.sound hP⟩⟩

/-- `isomorphismClassesEquivOfAlgebraExtension` sends the class of a solution `P` to the class of
its transport. -/
theorem isomorphismClassesEquivOfAlgebraExtension_mk (P : S.CompatibleFirstOrderThickening) :
    isomorphismClassesEquivOfAlgebraExtension S S' θ hθ θ' hθ' R hR
        (Quotient.mk (isomorphicSetoid S) P) =
      Quotient.mk (isomorphicSetoid S') (transportSolution S S' θ hθ θ' hθ' R hR P) :=
  rfl

end Transport

/-! ### Transporting a torsor -/

/-- **A principal homogeneous space transported along a bijection and an isomorphism of
groups**: if `P'` is a torsor under `G'`, `e : P ≃ P'` and `φ : G ≃+ G'`, then `P` is a torsor
under `G`, with `ξ +ᵥ p = e⁻¹(φ ξ +ᵥ e p)`. -/
@[instance_reducible]
def addTorsorTransfer {G G' P P' : Type*} [AddGroup G] [AddGroup G'] (T : AddTorsor G' P')
    (e : P ≃ P') (φ : G ≃+ G') : AddTorsor G P :=
  letI := T
  { vadd := fun ξ p => e.symm (φ ξ +ᵥ e p)
    zero_vadd := fun p => by
      change e.symm (φ 0 +ᵥ e p) = p
      simp
    add_vadd := fun ξ η p => by
      change e.symm (φ (ξ + η) +ᵥ e p) = e.symm (φ ξ +ᵥ e (e.symm (φ η +ᵥ e p)))
      simp [add_vadd]
    vsub := fun p q => φ.symm (e p -ᵥ e q)
    nonempty := ⟨e.symm (Classical.arbitrary P')⟩
    vsub_vadd' := fun p q => by
      change e.symm (φ (φ.symm (e p -ᵥ e q)) +ᵥ e q) = p
      simp
    vadd_vsub' := fun ξ p => by
      change φ.symm (e (e.symm (φ ξ +ᵥ e p)) -ᵥ e p) = ξ
      simp }

/-- In `addTorsorTransfer T e φ`, the action is `ξ +ᵥ p = e⁻¹(φ ξ +ᵥ e p)`. -/
theorem addTorsorTransfer_vadd {G G' P P' : Type*} [AddGroup G] [AddGroup G']
    (T : AddTorsor G' P') (e : P ≃ P') (φ : G ≃+ G') (ξ : G) (p : P) :
    (addTorsorTransfer T e φ).vadd ξ p = e.symm (T.vadd (φ ξ) (e p)) :=
  rfl

end Deformation.ToposThickening.RingedToposExtensionProblem

end
