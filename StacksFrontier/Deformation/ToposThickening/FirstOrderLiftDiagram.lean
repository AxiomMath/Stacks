module

public import StacksFrontier.Deformation.ToposThickening.SectionwiseDerivation

/-!
# The diagram of Stacks 08U8/08UG on one site, with the source's compatibility of `ν`

The lifting lemmas [Stacks Project, Tag 08U8] (ringed spaces) and [Stacks Project, Tag 08UG]
(ringed topoi) start from a commutative diagram of two first order thickenings over two first
order thickenings of bases, a comparison of the two layers, and a `g`-map `ν : 𝒢₁ ⟶ 𝒢₂` of the
two ideal modules making the diagram of ideal rows (Tags 08UA, 08UI) commute. The proofs reduce
to the case where all the sheaves of rings live on one site. This file records that one-site
diagram, `Deformation.ToposThickening.FirstOrderLiftDiagram`, the lifts of it, and the principal
homogeneous space structure on the lifts under its derivations.

## Main definitions

* `Deformation.ToposThickening.FirstOrderLiftDiagram`: the one-site diagram.
* `Deformation.ToposThickening.FirstOrderLiftDiagram.Lift`: a homomorphism `𝒪'₁ ⟶ 𝒪'₂` of
  sheaves of commutative rings fitting into the diagram compatibly with `ν`.
* `Deformation.ToposThickening.FirstOrderLiftDiagram.translate`: translation of a lift by a
  derivation of the diagram.

## Main results

* `Deformation.ToposThickening.FirstOrderLiftDiagram.translate_zero` and `translate_add`: the
  action of the derivations on the lifts. That it is simply transitive is
  `Deformation.ToposThickening.FirstOrderLiftDiagram.existsUnique_translateHom`
  (`StacksFrontier/Deformation/ToposThickening/LiftingDerivationGroup.lean`), with the source's
  own acting group.

## Implementation notes

**Why not `Deformation.ToposThickening.LiftDiagram`.** That structure, in
`StacksFrontier/Deformation/ToposThickening/LiftingBetweenThickenings.lean`, asks for the
compatibility `f'₂(gB'(a)) = ν(f'₁(a))` of `ν` with the base for *every* section `a` of the
thickened base `𝒪_{B'₁}` whose image `f'₁(a)` lies in `𝒢₁`. The source's diagram of ideal rows
asks it only for the sections of the base *ideal* `𝒥₁ = Ker(𝒪_{B'₁} ⟶ 𝒪_{B₁})`. The two differ:
take `S'₁ = S₁ = Spec k[x]`, `X'₁ = X₁ = Spec k` over `x ↦ 0`, `S₂ = X₂ = Spec k` and
`S'₂ = X'₂ = Spec k[ε]` with `S'₂ ⟶ S'₁` given by `x ↦ ε`; then `x` is killed in `𝒪_{X₁}` but not
in the base, and `f'₂(gB'(x)) = ε ≠ 0 = ν(f'₁(x))`. That situation satisfies the source's
hypotheses — and has no lift, its obstruction class being the nonzero class of
`ε ∈ Hom(H⁻¹(NL_{X₁/S₁}), 𝒢₂)` — but is not a `LiftDiagram`. The field `nu_base` below is the
source's condition: it carries the hypothesis `front.baseReduction a = 0`.

**What is shared with `LiftDiagram`, and what is not.** The structure differs from
`Deformation.ToposThickening.LiftDiagram` exactly by the field `nu_base`; every other field is
the same, and its two layers are the base's `Deformation.ToposThickening.LiftSquare`. The
derivations acting on the lifts are the base's `Deformation.ToposThickening.Derivation` of the
derivation situation of the diagram, with the additive group of
`StacksFrontier/Deformation/ToposThickening/SectionwiseDerivation.lean`. The lifts cannot be the
base's `LiftDiagram.Lift`, whose type is indexed by a `LiftDiagram` and so requires the stronger
compatibility; they are recorded here with their two compatibilities with the reductions and
the bases stated section by section (`Lift.reduction_app`, `Lift.base_app`), the morphism forms
being `Lift.reduction_comm` and `Lift.base_comm`.

## References

* [Stacks Project, Tag 08U8](https://stacks.math.columbia.edu/tag/08U8)
* [Stacks Project, Tag 08UA](https://stacks.math.columbia.edu/tag/08UA)
* [Stacks Project, Tag 08UG](https://stacks.math.columbia.edu/tag/08UG)
* [Stacks Project, Tag 08UI](https://stacks.math.columbia.edu/tag/08UI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v u w v₂ u₂ v₃ u₃

namespace Deformation.ToposThickening

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- **The diagram of [Stacks Project, Tag 08U8] and [Stacks Project, Tag 08UG] on one site.**
Two layers — each a first order thickening `𝒪_{B'} ⟶ 𝒪_B` of a base, a first order thickening
`𝒪' ⟶ 𝒪` of the source over it, and the module `𝒢` identified with the ideal of the source
thickening — the comparison morphisms `g`, `gB`, `gB'` from the index `1` layer to the index `2`
layer (the direction of `g⁻¹` in the source, the underlying spaces being identified), and the
comparison `ν` of the two ideal modules, compatible with the two maps out of the base ideals as
the diagram of ideal rows of Tags 08UA and 08UI says: for a section `a` of the base ideal `𝒥₁`,
`ν(c₁(a)) = c₂(gB'(a))`. The comparison of the two thickened sources is absent: producing it is
the lifting problem. -/
structure FirstOrderLiftDiagram where
  /-- The front layer, index `1` in the source. -/
  front : LiftSquare J
  /-- The back layer, index `2` in the source. -/
  back : LiftSquare J
  /-- The comparison of the reduced source structure sheaves. -/
  g : front.O ⟶ back.O
  /-- The comparison of the reduced base structure sheaves. -/
  gB : front.OB ⟶ back.OB
  /-- The comparison of the thickened base structure sheaves. -/
  gB' : front.OB' ⟶ back.OB'
  /-- The comparison of sources lies over the comparison of bases. -/
  g_comm : gB ≫ back.f = front.f ≫ g
  /-- The square of bases commutes. -/
  gB_comm : gB' ≫ back.baseReduction = front.baseReduction ≫ gB
  /-- The comparison of the two ideal modules, linear over the front structure sheaf. -/
  nu : front.G ⟶ (SheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map g)).obj back.G
  /-- The comparison of ideals is compatible with the two maps out of the base ideals: for a
  section `a` of the base ideal `𝒥₁ = Ker(𝒪_{B'₁} ⟶ 𝒪_{B₁})`, whose image `f'₁(a)` is the image
  of a section `m` of `𝒢₁`, the image `f'₂(gB'(a))` is the image of `ν(m)`. -/
  nu_base : ∀ (U : Cᵒᵖ) (a : front.OB'.obj.obj U) (m : front.G.val.obj U),
    front.baseReduction.hom.app U a = 0 →
      front.f'.hom.app U a = front.incl m →
        back.f'.hom.app U (gB'.hom.app U a) =
          back.incl (show back.G.val.obj U from nu.val.app U m)

namespace FirstOrderLiftDiagram

variable {J}

/-- The comparison of the two ideal modules, on sections. -/
noncomputable def nuSection (D : FirstOrderLiftDiagram J) {U : Cᵒᵖ} (m : D.front.G.val.obj U) :
    D.back.G.val.obj U :=
  D.nu.val.app U m

/-- The comparison of ideal modules is additive on sections. -/
theorem nuSection_add (D : FirstOrderLiftDiagram J) {U : Cᵒᵖ} (m n : D.front.G.val.obj U) :
    D.nuSection (m + n) = D.nuSection m + D.nuSection n :=
  map_add (D.nu.val.app U).hom m n

/-- A morphism fitting into the diagram of [Stacks Project, Tag 08UG] compatibly with `ν`: with
the underlying topoi identified, a homomorphism `O'₁ ⟶ O'₂` of sheaves of commutative rings
commuting with the two reductions, with the two structure maps from the thickened bases, and
inducing `ν` on the two ideals. -/
@[ext]
structure Lift (D : FirstOrderLiftDiagram J) where
  /-- The homomorphism of the two thickened structure sheaves. -/
  hom : D.front.O' ⟶ D.back.O'
  /-- It is over the comparison of the reduced structure sheaves, section by section. -/
  reduction_app : ∀ (U : Cᵒᵖ) (a : D.front.O'.obj.obj U),
    D.back.reduction.hom.app U (hom.hom.app U a) = D.g.hom.app U (D.front.reduction.hom.app U a)
  /-- It is under the comparison of the thickened base structure sheaves, section by section. -/
  base_app : ∀ (U : Cᵒᵖ) (a : D.front.OB'.obj.obj U),
    hom.hom.app U (D.front.f'.hom.app U a) = D.back.f'.hom.app U (D.gB'.hom.app U a)
  /-- It induces `ν` on the two ideals. -/
  kernel_comm : ∀ (U : Cᵒᵖ) (m : D.front.G.val.obj U),
    hom.hom.app U (D.front.incl m) = D.back.incl (D.nuSection m)

namespace Lift

variable {D : FirstOrderLiftDiagram J}

/-- A lift is over the comparison of the reduced structure sheaves. -/
theorem reduction_comm (p : Lift D) :
    p.hom ≫ D.back.reduction = D.front.reduction ≫ D.g :=
  sheafHom_ext J fun U a => p.reduction_app U a

/-- A lift is under the comparison of the thickened base structure sheaves. -/
theorem base_comm (p : Lift D) : D.front.f' ≫ p.hom = D.gB' ≫ D.back.f' :=
  sheafHom_ext J fun U a => p.base_app U a

end Lift

/-! ### The principal homogeneous space structure, proved for the concrete acting group -/

/-- The derivation situation of the diagram: its front square, with values in the ideal module
of the back square through the comparison `g`. The derivations of the diagram are exactly the
derivations of this situation, so they carry the additive group of
`Deformation.ToposThickening.Derivation`. -/
noncomputable abbrev toSituation (D : FirstOrderLiftDiagram J) : DerivationSituation J where
  O := D.front.O
  O' := D.front.O'
  OB' := D.front.OB'
  reduction := D.front.reduction
  f' := D.front.f'
  I := D.front.G
  inclusion := D.front.kernelInclusion
  Otarget := D.back.O
  g := D.g
  G := D.back.G

/-- The ideal inclusion of the situation of a diagram is the one of its front square. -/
@[simp]
theorem toSituation_incl (D : FirstOrderLiftDiagram J) {U : Cᵒᵖ} (m : D.front.G.val.obj U) :
    D.toSituation.incl m = D.front.incl m := rfl

/-- The base structure map of the situation of a diagram is the one of its front square. -/
@[simp]
theorem toSituation_f' (D : FirstOrderLiftDiagram J) : D.toSituation.f' = D.front.f' := rfl

/-- Translating a lift of the diagram by a derivation: the homomorphism
`x ↦ φ(x) + δ(x)`. -/
noncomputable def translate {D : FirstOrderLiftDiagram J} (p : Lift D)
    (δ : Derivation D.toSituation) : Lift D where
  hom := ObjectProperty.homMk
    { app := fun U => CommRingCat.ofHom
        { toFun := fun x => p.hom.hom.app U x + D.back.incl (δ.toFun U x)
          map_one' := by
            rw [δ.map_one U, D.back.incl_zero, add_zero]
            simp
          map_mul' := fun x y => by
            have hqx : p.hom.hom.app U x * D.back.incl (δ.toFun U y) =
                D.back.incl (toRingSection J
                  (D.g.hom.app U (D.front.reduction.hom.app U x)) • δ.toFun U y) := by
              rw [D.back.mul_incl, p.reduction_app U _]
            have hpy : p.hom.hom.app U y * D.back.incl (δ.toFun U x) =
                D.back.incl (toRingSection J
                  (D.g.hom.app U (D.front.reduction.hom.app U y)) • δ.toFun U x) := by
              rw [D.back.mul_incl, p.reduction_app U _]
            have h0 : D.back.incl (δ.toFun U x) * D.back.incl (δ.toFun U y) = 0 :=
              D.back.incl_mul_incl _ _
            have hp : p.hom.hom.app U (x * y) =
                p.hom.hom.app U x * p.hom.hom.app U y := by simp
            rw [hp, δ.leibniz U x y, D.back.incl_add, ← hqx, ← hpy]
            linear_combination -h0
          map_zero' := by rw [δ.map_zero U, D.back.incl_zero, add_zero]; simp
          map_add' := fun x y => by
            have hp : p.hom.hom.app U (x + y) =
                p.hom.hom.app U x + p.hom.hom.app U y := by simp
            rw [hp, δ.map_add' U x y, D.back.incl_add]
            abel }
      naturality := fun {U V} h => by
        refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
        change p.hom.hom.app V (D.front.O'.obj.map h x) +
            D.back.incl (δ.toFun V (D.front.O'.obj.map h x)) =
          D.back.O'.obj.map h (p.hom.hom.app U x + D.back.incl (δ.toFun U x))
        rw [δ.naturality h x, D.back.incl_naturality, sheafHom_naturality_apply]
        exact (map_add _ _ _).symm }
  reduction_app := fun U x => by
    change D.back.reduction.hom.app U
        (p.hom.hom.app U x + D.back.incl (δ.toFun U x)) =
      D.g.hom.app U (D.front.reduction.hom.app U x)
    rw [map_add, D.back.reduction_incl, add_zero, p.reduction_app U _]
  base_app := fun U a => by
    change p.hom.hom.app U (D.toSituation.f'.hom.app U a) +
        D.back.incl (δ.toFun U (D.toSituation.f'.hom.app U a)) =
      D.back.f'.hom.app U (D.gB'.hom.app U a)
    rw [δ.map_base U a, D.back.incl_zero, add_zero]
    simp only
    exact p.base_app U a
  kernel_comm := fun U m => by
    change p.hom.hom.app U (D.toSituation.incl m) +
      D.back.incl (δ.toFun U (D.toSituation.incl m)) = D.back.incl (D.nuSection m)
    rw [δ.map_kernel U m, D.back.incl_zero, add_zero]
    simp only [toSituation_incl]
    exact p.kernel_comm U m

/-- The formula determining a translate. -/
@[simp]
theorem translate_apply {D : FirstOrderLiftDiagram J} (p : Lift D) (δ : Derivation D.toSituation)
    (U : Cᵒᵖ) (x : D.front.O'.obj.obj U) :
    (translate p δ).hom.hom.app U x = p.hom.hom.app U x + D.back.incl (δ.toFun U x) := rfl

/-- The zero derivation acts trivially. -/
theorem translate_zero {D : FirstOrderLiftDiagram J} (p : Lift D) : translate p 0 = p := by
  refine Lift.ext (sheafHom_ext J fun U x => ?_)
  rw [translate_apply, Derivation.zero_toFun, D.back.incl_zero, add_zero]

/-- The action of derivations on lifts is additive. -/
theorem translate_add {D : FirstOrderLiftDiagram J} (p : Lift D) (δ ε : Derivation D.toSituation) :
    translate (translate p δ) ε = translate p (δ + ε) := by
  refine Lift.ext (sheafHom_ext J fun U x => ?_)
  rw [translate_apply, translate_apply, translate_apply, Derivation.add_toFun,
    D.back.incl_add]
  abel


end FirstOrderLiftDiagram


end Deformation.ToposThickening

end
