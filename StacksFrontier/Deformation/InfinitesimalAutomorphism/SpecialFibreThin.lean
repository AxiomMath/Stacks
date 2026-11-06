module

public import StacksFrontier.Deformation.Cofibered.FibreThin
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.TangentTensor

/-!
# The residue field under the base, and automorphisms over it

Let `p : F ⥤ 𝒞_Λ` be cofibered in groupoids and let `x` be an object of `F`. The residue field
read as an algebra under the base of `x` is `Deformation.specialFibreUnder`, whose underlying
object of `𝒞_Λ` has the same carrier `ULift k` as the residue-field object
`Deformation.residueFieldObject` but a different, propositionally equal, structural
`Λ`-algebra map. The two are therefore isomorphic and not equal, and this file supplies that
isomorphism at an arbitrary universe for the carriers of `𝒞_Λ` — the universe at which the
six-term sequence of a `2`-fibre product is stated.

Its consequence is the one needed there: the fibre of `p` over the residue field under the
base is thin whenever the fibre over the residue-field object is
(`Deformation.isThin_specialFiber` for a predeformation category), and over a thin fibre the
chosen pushforward of `x` has no nontrivial automorphism, so *every* automorphism of `x[M]` is
infinitesimal.

## Main definitions

* `Deformation.specialFibreUnderRightCompare`, its inverse
  `Deformation.specialFibreUnderRightCompareInv`: the identity of `ULift k`, read as a
  morphism of `𝒞_Λ` between the two presentations of the residue field.
* `Deformation.specialFibreUnderRightIso`: the resulting isomorphism.

## Main results

* `Deformation.hom_specialFibreUnderRight_ext`: morphisms of `𝒞_Λ` into the residue field
  under the base of `x` are unique.
* `Deformation.isThin_fiber_specialFibreUnder_right`: the fibre over the residue field under
  the base of `x` is thin as soon as the fibre over the residue-field object is.
* `Deformation.ker_transportAutHom_eq_top_of_isThin`,
  `Deformation.ker_transportAutHom_squareZeroUnderRed_eq_top`: over a thin special fibre the
  infinitesimal automorphisms of a pushforward are all of its automorphisms.
-/

@[expose] public section

namespace Deformation

/-! ### The residue field under the base at an arbitrary carrier universe -/

section
open CategoryTheory IsLocalRing
universe u v w u₁ v₁

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {F : Type u₁} [Category.{v₁} F] {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k} (x : F)

/-- The residue of a structural scalar is that scalar. -/
private theorem residueEquiv_residue_algebraMap_apply
    (B : ArtinianLocalAlgCat.{u, max v w, w} Λ k) (t : Λ) :
    B.residueEquiv (residue B (algebraMap Λ B t)) = algebraMap Λ k t := by
  rw [show residue B (algebraMap Λ B t) = algebraMap Λ (ResidueField B) t by
    rw [IsScalarTower.algebraMap_apply Λ B (ResidueField B) t]
    simp only [IsLocalRing.ResidueField.algebraMap_eq]]
  exact B.residueEquiv.commutes t

/-- The identity of `ULift k`, read as a morphism of `𝒞_Λ` from the residue-field object to
the residue field regarded as an algebra under the base of `x`. The two objects have the same
carrier, the same ring and the same reduction; only the structural `Λ`-algebra maps differ,
and they are propositionally equal. -/
public noncomputable def specialFibreUnderRightCompare :
    residueFieldObject.{u, v, w} Λ k ⟶
      (specialFibreUnder.{u, v, w, u₁, v₁} (p := p) (x := x)).right where
  hom :=
    { toFun := fun z => z
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun t => by
        change ULift.up (algebraMap Λ k t) =
          ULift.up ((p.obj x).residueEquiv (residue (p.obj x) (algebraMap Λ (p.obj x) t)))
        rw [residueEquiv_residue_algebraMap_apply (p.obj x) t] }
  isLocal := ⟨fun _ ha => ha⟩
  residue_comm := fun _ => rfl

/-- The identity of `ULift k`, read as a morphism of `𝒞_Λ` from the residue field regarded as
an algebra under the base of `x` back to the residue-field object. -/
public noncomputable def specialFibreUnderRightCompareInv :
    (specialFibreUnder.{u, v, w, u₁, v₁} (p := p) (x := x)).right ⟶
      residueFieldObject.{u, v, w} Λ k where
  hom :=
    { toFun := fun z => z
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun t => by
        change ULift.up ((p.obj x).residueEquiv
            (residue (p.obj x) (algebraMap Λ (p.obj x) t))) =
          ULift.up (algebraMap Λ k t)
        rw [residueEquiv_residue_algebraMap_apply (p.obj x) t] }
  isLocal := ⟨fun _ ha => ha⟩
  residue_comm := fun _ => rfl

/-- **The residue field under the base is the residue-field object of `𝒞_Λ`**, at an arbitrary
universe for the carriers: the two presentations are identified by the identity of `ULift k`
in both directions. -/
public noncomputable def specialFibreUnderRightIso :
    residueFieldObject.{u, v, w} Λ k ≅
      (specialFibreUnder.{u, v, w, u₁, v₁} (p := p) (x := x)).right where
  hom := specialFibreUnderRightCompare.{u, v, w, u₁, v₁} (p := p) x
  inv := specialFibreUnderRightCompareInv.{u, v, w, u₁, v₁} (p := p) x
  hom_inv_id := ArtinianLocalAlgCat.hom_ext (AlgHom.ext fun _ => rfl)
  inv_hom_id := ArtinianLocalAlgCat.hom_ext (AlgHom.ext fun _ => rfl)

/-- Any two morphisms of `𝒞_Λ` into the residue field under the base agree: that object is
isomorphic to the residue-field object, into which morphisms are unique. -/
public theorem hom_specialFibreUnderRight_ext
    {B : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (f₁ f₂ : B ⟶ (specialFibreUnder.{u, v, w, u₁, v₁} (p := p) (x := x)).right) : f₁ = f₂ :=
  (cancel_mono (specialFibreUnderRightIso.{u, v, w, u₁, v₁} (p := p) x).inv).1
    (hom_residueFieldObject_ext.{u, v, w} _ _)

end

/-! ### Automorphisms over the residue field under the base -/

section
open CategoryTheory IsLocalRing
universe u v w u₁ v₁

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {F : Type u₁} [Category.{v₁} F] {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k} (x : F)

/-- The fibre of `p` over the residue field read as an algebra under the base of `x` is thin
as soon as the fibre over the residue-field object is, the two base objects being isomorphic.
For a predeformation category the hypothesis is `Deformation.isThin_specialFiber`. -/
public theorem isThin_fiber_specialFibreUnder_right (hp : IsCofiberedInGroupoids p)
    (hthin : Quiver.IsThin (p.Fiber (residueFieldObject.{u, v, w} Λ k))) :
    Quiver.IsThin (p.Fiber (specialFibreUnder.{u, v, w, u₁, v₁} (p := p) (x := x)).right) :=
  isThin_fiber_of_iso hp (specialFibreUnderRightIso.{u, v, w, u₁, v₁} (p := p) x) hthin

variable {x}

/-- **Over a thin special fibre every automorphism is infinitesimal.** The chosen pushforward
of `x` to the residue field under the base lies in a thin fibre, so its automorphism group is
trivial and the transport homomorphism to it has everything in its kernel. -/
public theorem ker_transportAutHom_eq_top_of_isThin (hp : IsCofiberedInGroupoids p)
    (P : ChosenPushforwardsAt p x)
    (hthin : Quiver.IsThin (p.Fiber (residueFieldObject.{u, v, w} Λ k)))
    {U : Under (p.obj x)} (r : U ⟶ specialFibreUnder.{u, v, w, u₁, v₁} (p := p) (x := x)) :
    MonoidHom.ker (P.transportAutHom r) = ⊤ := by
  have hsub := isThin_fiber_specialFibreUnder_right.{u, v, w, u₁, v₁} (p := p) x hp hthin
    (P.obj (specialFibreUnder.{u, v, w, u₁, v₁} (p := p) (x := x)))
    (P.obj (specialFibreUnder.{u, v, w, u₁, v₁} (p := p) (x := x)))
  exact (Subgroup.eq_top_iff' _).2 fun _ =>
    MonoidHom.mem_ker.2 (Aut.ext (Iso.ext (Subsingleton.elim _ _)))

/-- **Every automorphism of `x[M]` is infinitesimal over a thin special fibre.** The
infinitesimal automorphisms of the chosen pushforward of `x` to the square-zero extension by
`M` are, relative to the reduction to the residue field under the base, all of its
automorphisms. -/
public theorem ker_transportAutHom_squareZeroUnderRed_eq_top (hp : IsCofiberedInGroupoids p)
    (P : ChosenPushforwardsAt p x)
    (hthin : Quiver.IsThin (p.Fiber (residueFieldObject.{u, v, w} Λ k)))
    (M : FGModuleCat.{max v w} k) :
    MonoidHom.ker (P.transportAutHom (squareZeroUnderRed.{u, v, w, u₁, v₁} p x M)) = ⊤ :=
  ker_transportAutHom_eq_top_of_isThin.{u, v, w, u₁, v₁} hp P hthin _

end

end Deformation

end
