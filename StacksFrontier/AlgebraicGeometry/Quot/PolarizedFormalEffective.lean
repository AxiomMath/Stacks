module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedStackUnconditional
public import StacksFrontier.Deformation.Artin.FormalObject.Realization
public import StacksFrontier.Deformation.Artin.FormalObject.BaseContains
public import StacksFrontier.Deformation.Artin.FormalObject.NonEffectiveSystem
public import StacksFrontier.AlgebraicGeometry.RelativeAmpleAffineBase.Basic
public import StacksFrontier.AlgebraicGeometry.PolarizedAlgebraization.StrongFormalEffectiveness

/-!
# Formal objects of `𝒫olarized` are effective (Stacks 0D4U)

A formal object `ξ = (R, ξ_n, f_n)` of the stack `𝒫olarized` of polarized proper schemes
(**Stacks 07X4**, **0D1M**) consists of a Noetherian complete local ring `R`, polarized families
`(X_n ⟶ Spec(R / 𝔪^{n+1}), ℒ_n)` and morphisms of polarized families `ξ_n ⟶ ξ_{n+1}` over the
inclusions of the infinitesimal thickenings. A morphism of polarized families is a cartesian square
with an isomorphism of polarizations, so `ξ` is exactly the data of Stacks 0D4T for the inverse
system `R_n = R / 𝔪^{n+1}`, whose transition maps are surjective with nilpotent kernels and whose
limit is `R` because `R` is complete. Stacks 0D4T then algebraizes `ξ`, and the algebraization is
an object of `𝒫olarized` over `Spec R` restricting to `ξ`, i.e. `ξ` is effective (**Stacks 07X7**).

This file carries out that reduction and applies Stacks 0D4T
(`Stacks.PolarizedAlgebraization.exists_algebraization`).

## Main definitions

* `AlgebraicGeometry.PolarizedFormal.powQuotientRingDiagram`: the inverse system of rings
  `n ↦ A ⧸ I ^ (n + 1)`, and `powQuotientRingConeIsLimit`: an `I`-adically complete ring is its
  limit.
* `AlgebraicGeometry.PolarizedFormal.Algebraization`: a polarized family over `Spec R` with
  compatible identifications of its restrictions to the thickenings with the levels of `ξ`.
* `AlgebraicGeometry.PolarizedFormal.Algebraization.ofLimit`: an algebraization from data over the
  limit `Spec (lim R ⧸ 𝔪^{n+1})`, the form in which Stacks 0D4T produces it.

## Main results

* `AlgebraicGeometry.PolarizedFormal.isPullback_transition`,
  `AlgebraicGeometry.PolarizedFormal.isAmple_level_zero` and the surjectivity and nilpotence of the
  transition maps of `ringSystem`: the levels of a formal object satisfy the hypotheses of
  Stacks 0D4T.
* `AlgebraicGeometry.PolarizedFormal.isEffective_of_algebraization`: an algebraized formal object
  is effective.
* `AlgebraicGeometry.PolarizedFormal.nonempty_algebraization`: every formal object of `𝒫olarized`
  has an algebraization (Stacks 0D4T).
* `AlgebraicGeometry.PolarizedFormal.isEffective`: every formal object of `𝒫olarized` over a
  terminal base is effective, and `AlgebraicGeometry.polarizedFormalObject_isEffective`:
  **Stacks 0D4U**, over `Spec ℤ`.

## Implementation notes

The levels of a formal object lie over the thickenings only up to an equality of objects of the
site, so their structure morphisms are transported to the thickenings with `eqToHom`
(`AlgebraicGeometry.PolarizedFormal.levelToTruncation`). The base of the stack is a terminal object
of the site, as `Spec ℤ` is, so `𝒫olarized` is read through
`AlgebraicGeometry.polarizedSliceProjection`.

## References

* [Stacks Project, Tag 0D4U](https://stacks.math.columbia.edu/tag/0D4U)
* [Stacks Project, Tag 0D4T](https://stacks.math.columbia.edu/tag/0D4T)
* [Stacks Project, Tag 07X4](https://stacks.math.columbia.edu/tag/07X4)
* [Stacks Project, Tag 07X7](https://stacks.math.columbia.edu/tag/07X7)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits IsLocalRing Deformation.Artin Opposite Stacks.Ample

namespace AlgebraicGeometry.PolarizedFormal

/-! ### The inverse system of truncations of a complete ring -/

section RingSystem

variable (A : Type u) [CommRing A] (I : Ideal A)

/-- The inverse system of commutative rings `n ↦ A ⧸ I ^ (n + 1)`, with the quotient maps as its
transition maps. -/
def powQuotientRingDiagram : ℕᵒᵖ ⥤ CommRingCat.{u} where
  obj n := CommRingCat.of (A ⧸ I ^ (n.unop + 1))
  map f := CommRingCat.ofHom (Ideal.Quotient.factorPow I (Nat.succ_le_succ (leOfHom f.unop)))
  map_id _ := by
    ext x
    rfl
  map_comp _ _ := by
    ext x
    rfl

/-- The cone of quotient maps `A ⟶ A ⧸ I ^ (n + 1)`. -/
def powQuotientRingCone : Cone (powQuotientRingDiagram A I) where
  pt := CommRingCat.of A
  π :=
    { app n := CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n.unop + 1)))
      naturality _ _ _ := by
        ext x
        rfl }

/-- The successor map on `ℕ` is strictly monotone. -/
theorem strictMono_add_one : StrictMono fun n : ℕ => n + 1 :=
  strictMono_nat_of_lt_succ fun _ => Nat.lt_succ_self _

variable {A I} in
/-- The components of a cone over the quotients `A ⧸ I ^ (n + 1)` are compatible with the quotient
maps. -/
theorem powQuotientRingCone_compat (s : Cone (powQuotientRingDiagram A I)) (m : ℕ) :
    (Ideal.Quotient.factorPow I (strictMono_add_one.monotone m.le_succ)).comp
      (s.π.app (op (m + 1))).hom = (s.π.app (op m)).hom :=
  congrArg CommRingCat.Hom.hom (s.w (homOfLE (Nat.le_succ m)).op)

variable {A I} [IsAdicComplete I A]

/-- The lift of a cone over the quotients `A ⧸ I ^ (n + 1)` to an `I`-adically complete `A`. -/
def powQuotientRingConeLift (s : Cone (powQuotientRingDiagram A I)) : s.pt.carrier →+* A :=
  IsAdicComplete.StrictMono.liftRingHom I strictMono_add_one
    (fun n => (s.π.app (op n)).hom) (fun {m} => powQuotientRingCone_compat s m)

/-- The lift of a cone composed with a quotient map is the component of the cone. -/
theorem powQuotientRingConeLift_fac (s : Cone (powQuotientRingDiagram A I)) (n : ℕ)
    (x : s.pt) :
    Ideal.Quotient.mk (I ^ (n + 1)) (powQuotientRingConeLift s x) = (s.π.app (op n)).hom x := by
  have := IsAdicComplete.StrictMono.mk_liftRingHom (a := fun n => n + 1) (n := n) I
    strictMono_add_one (fun n => (s.π.app (op n)).hom)
    (fun {m} => powQuotientRingCone_compat s m) x
  exact this

/-- The lift of a cone is the only ring map compatible with its components. -/
theorem powQuotientRingConeLift_uniq (s : Cone (powQuotientRingDiagram A I))
    (F : s.pt.carrier →+* A)
    (hF : ∀ n : ℕ, (Ideal.Quotient.mk (I ^ (n + 1))).comp F = (s.π.app (op n)).hom) :
    F = powQuotientRingConeLift s := by
  have := IsAdicComplete.StrictMono.eq_liftRingHom (a := fun n => n + 1) (F := F) I
    strictMono_add_one (f := fun n => (s.π.app (op n)).hom)
    (fun {m} => powQuotientRingCone_compat s m) hF
  exact this

variable (A I) in
/-- **An `I`-adically complete ring is the limit of its quotients `A ⧸ I ^ (n + 1)`.** -/
def powQuotientRingConeIsLimit : IsLimit (powQuotientRingCone A I) where
  lift s := CommRingCat.ofHom (powQuotientRingConeLift s)
  fac s n := CommRingCat.hom_ext (RingHom.ext fun x => powQuotientRingConeLift_fac s n.unop x)
  uniq s m hm := CommRingCat.hom_ext (powQuotientRingConeLift_uniq s m.hom fun n =>
    congrArg CommRingCat.Hom.hom (hm (op n)))

end RingSystem

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {hT : IsTerminal (B.obj hS)}
  (ξ : FormalObject B S hS (polarizedSliceProjection B hS hT))

/-- The base of the `n`-th level of a formal object of `𝒫olarized` is the `n`-th infinitesimal
thickening of its complete local base. -/
theorem level_base_eq (n : ℕ) : (ξ.level n).base = ⟨ξ.base.truncation n, ξ.contains n⟩ :=
  congrArg Comma.left (ξ.level_eq n)

/-- The scheme under the `n`-th level is the `n`-th infinitesimal thickening. -/
theorem level_scheme_eq (n : ℕ) :
    B.inclusion.obj (ξ.level n).base = ξ.base.truncation n :=
  congrArg B.inclusion.obj (level_base_eq ξ n)

/-- The structure morphism of the `n`-th level, to the `n`-th infinitesimal thickening. -/
def levelToTruncation (n : ℕ) : (ξ.level n).total ⟶ ξ.base.truncation n :=
  (ξ.level n).toBase ≫ eqToHom (level_scheme_eq ξ n)

/-- The base map of the transition of a formal object of `𝒫olarized` is the inclusion of one
infinitesimal thickening in the next. -/
theorem inclusion_map_transition_baseMap (n : ℕ) :
    B.inclusion.map (ξ.transition n).baseMap =
      eqToHom (level_scheme_eq ξ n) ≫ ξ.base.truncationSucc n ≫
        eqToHom (level_scheme_eq ξ (n + 1)).symm := by
  have h := congrArg (fun f => B.inclusion.map f.left) (FormalObject.map_transition ξ n)
  simp only [Over.comp_left, Over.eqToHom_left, Functor.map_comp, eqToHom_map] at h
  exact h

/-- **An algebraization of a formal object of `𝒫olarized`.** A polarized family over the complete
local base `Spec R` of the formal object, together with cartesian squares exhibiting each level
`X_n ⟶ Spec(R / 𝔪^{n+1})` as its base change, and isomorphisms of the pulled back polarization
with the polarization of the level, all compatible with the transitions of the formal object.
These are the "isomorphisms `X_n ≅ X ×_S S_n` and `ℒ_n ≅ ℒ|_{X_n}` compatible with the morphisms
`i_n` and `φ_n`" of Stacks 0D4T. -/
structure Algebraization where
  /-- The total space. -/
  X : Scheme.{u}
  /-- The structure morphism to the complete local base. -/
  toBase : X ⟶ Spec (.of ξ.base.R)
  /-- The structure morphism is proper. -/
  proper : IsProper toBase
  /-- The structure morphism is flat. -/
  flat : Flat toBase
  /-- The structure morphism is of finite presentation. -/
  finitePresentation : FinitePresentation toBase
  /-- The polarization. -/
  L : X.Modules
  /-- The polarization is invertible. -/
  invertible : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L
  /-- The polarization is relatively ample. -/
  relativelyAmple : letI := invertible; Stacks.RelativeAmple.IsRelativelyAmple toBase L
  /-- The maps from the total spaces of the levels. -/
  j : ∀ n, (ξ.level n).total ⟶ X
  /-- Each level is the base change to its infinitesimal thickening. -/
  isPullback : ∀ n, IsPullback (j n) (levelToTruncation ξ n) toBase
    (adicThickeningι ξ.base.R (maximalIdeal ξ.base.R) n)
  /-- The maps from the levels are compatible with the transitions. -/
  transition_j : ∀ n, (ξ.transition n).totalMap ≫ j (n + 1) = j n
  /-- The comparisons of polarizations. -/
  ψ : ∀ n, (Scheme.Modules.pullback (j n)).obj L ≅ (ξ.level n).lineBundle
  /-- The comparisons of polarizations are compatible with those of the transitions. -/
  transition_ψ : ∀ n,
    (Scheme.Modules.pullbackComp (ξ.transition n).totalMap (j (n + 1))).symm.app L ≪≫
      (Scheme.Modules.pullback (ξ.transition n).totalMap).mapIso (ψ (n + 1)) ≪≫
        (ξ.transition n).lineBundleIso ≍ ψ n

namespace Algebraization

variable {ξ} (a : Algebraization ξ) (hA : B.Contains (Spec (.of ξ.base.R)))

/-- The polarized family of an algebraization, over the complete local base in the site. -/
def family : PolarizedFamily B where
  base := B.obj hA
  total := a.X
  toBase := a.toBase
  proper := a.proper
  flat := a.flat
  finitePresentation := a.finitePresentation
  lineBundle := a.L
  invertible := a.invertible
  relativelyAmple := a.relativelyAmple

/-- The polarized family of an algebraization lies over the complete local base. -/
theorem obj_family :
    (polarizedSliceProjection B hS hT).obj (a.family hA) = baseOver B S hS ξ.base hA :=
  (polarizedProjection B).sliceAtTerminal_obj_eq hT rfl

/-- The base map from the `n`-th level to the complete local base. -/
def levelBaseMap (n : ℕ) : (ξ.level n).base ⟶ B.obj hA :=
  eqToHom (level_base_eq ξ n) ≫
    ObjectProperty.homMk (X := ⟨ξ.base.truncation n, ξ.contains n⟩) (Y := B.obj hA)
      (adicThickeningι ξ.base.R (maximalIdeal ξ.base.R) n)

/-- The base map from a level is the inclusion of the infinitesimal thickening. -/
theorem inclusion_map_levelBaseMap (n : ℕ) :
    B.inclusion.map (levelBaseMap hA n) =
      eqToHom (level_scheme_eq ξ n) ≫ adicThickeningι ξ.base.R (maximalIdeal ξ.base.R) n := by
  rw [levelBaseMap, Functor.map_comp, eqToHom_map]
  rfl

/-- The morphism of polarized families from the `n`-th level to the algebraization. -/
def levelHom (n : ℕ) : ξ.level n ⟶ a.family hA where
  baseMap := levelBaseMap hA n
  totalMap := a.j n
  cartesian := by
    change IsPullback (a.j n) (ξ.level n).toBase a.toBase (B.inclusion.map (levelBaseMap hA n))
    rw [inclusion_map_levelBaseMap]
    refine (a.isPullback n).of_iso (Iso.refl _) (Iso.refl _)
      (eqToIso (level_scheme_eq ξ n).symm) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simp [levelToTruncation]
    · simp
    · simp
  lineBundleIso := a.ψ n

/-- An algebraization realizes the formal object. -/
def realization : FormalObject.Realization ξ hA (a.family hA) (a.obj_family hA) where
  r := a.levelHom hA
  comp_transition n := by
    refine PolarizedFamily.Hom.ext ?_ ?_ ?_
    · apply B.inclusion.map_injective
      change B.inclusion.map ((ξ.transition n).baseMap ≫ levelBaseMap hA (n + 1)) =
        B.inclusion.map (levelBaseMap hA n)
      rw [Functor.map_comp, inclusion_map_levelBaseMap, inclusion_map_levelBaseMap,
        inclusion_map_transition_baseMap]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      congr 1
      exact adicThickeningSucc_ι _ _ n
    · exact a.transition_j n
    · exact a.transition_ψ n
  map_eq n := by
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, Over.eqToHom_left]
    change levelBaseMap hA n = _
    rw [← Category.assoc]
    exact (Category.comp_id _).symm

end Algebraization

/-! ### The tower of a formal object -/

section Tower

/-- The inverse system of rings `R ⧸ 𝔪 ^ (n + 1)` of a formal object. -/
abbrev ringSystem : ℕᵒᵖ ⥤ CommRingCat.{u} :=
  powQuotientRingDiagram ξ.base.R (maximalIdeal ξ.base.R)

/-- The complete local ring of a formal object is the limit of its truncations. -/
def ringSystemIsLimit :
    IsLimit (powQuotientRingCone ξ.base.R (maximalIdeal ξ.base.R)) :=
  letI := ξ.base.complete
  powQuotientRingConeIsLimit _ _

/-- The transition maps of the inverse system of truncations are surjective. -/
theorem surjective_ringSystem_map (n : ℕ) :
    Function.Surjective ((ringSystem ξ).map (homOfLE (Nat.le_succ n)).op).hom :=
  Ideal.Quotient.factor_surjective
    (Ideal.pow_le_pow_right (Nat.succ_le_succ (Nat.le_succ n)))

/-- The kernels of the transition maps of the inverse system of truncations are nil. -/
theorem ker_ringSystem_map_le_nilradical (n : ℕ) :
    RingHom.ker ((ringSystem ξ).map (homOfLE (Nat.le_succ n)).op).hom ≤
      nilradical ((ringSystem ξ).obj (op (n + 1))) := fun x hx =>
  mem_nilradical.mpr (locallyNilpotent_ker_factor_pow (I := maximalIdeal ξ.base.R)
    (a := n + 1) (b := n + 1 + 1) (Nat.succ_ne_zero n)
    (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))) x hx)

/-- The transition squares of the levels of a formal object of `𝒫olarized` are cartesian over
the inclusions of successive infinitesimal thickenings. -/
theorem isPullback_transition (n : ℕ) :
    IsPullback (ξ.transition n).totalMap (levelToTruncation ξ n) (levelToTruncation ξ (n + 1))
      (Spec.map ((ringSystem ξ).map (homOfLE (Nat.le_succ n)).op)) := by
  refine (ξ.transition n).cartesian.of_iso (Iso.refl _) (Iso.refl _)
    (eqToIso (level_scheme_eq ξ n)) (eqToIso (level_scheme_eq ξ (n + 1))) ?_ ?_ ?_ ?_
  · simp
  · simp [levelToTruncation]
  · simp [levelToTruncation]
  · rw [inclusion_map_transition_baseMap]
    simp only [eqToIso.hom, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    rfl

/-- The structure morphism of a level to its thickening is proper. -/
instance isProper_levelToTruncation (n : ℕ) : IsProper (levelToTruncation ξ n) := by
  have := (ξ.level n).proper
  unfold levelToTruncation
  infer_instance

/-- The structure morphism of a level to its thickening is flat. -/
instance flat_levelToTruncation (n : ℕ) : Flat (levelToTruncation ξ n) := by
  have := (ξ.level n).flat
  unfold levelToTruncation
  infer_instance

/-- The structure morphism of a level to its thickening is of finite presentation. -/
theorem finitePresentation_levelToTruncation (n : ℕ) :
    FinitePresentation (levelToTruncation ξ n) := by
  obtain ⟨_, _, _⟩ := (ξ.level n).finitePresentation
  unfold levelToTruncation
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- The polarizations of the levels are invertible. -/
theorem isInvertibleModule_level (n : ℕ) :
    IsInvertibleModule (ξ.level n).total (ξ.level n).lineBundle :=
  (ξ.level n).invertible

/-- The polarization of the closed-point level is ample: it is relatively ample over the affine
scheme `Spec(R / 𝔪)` (Stacks 01VK). -/
theorem isAmple_level_zero :
    letI := isInvertibleModule_level ξ 0
    IsAmple (ξ.level 0).total (ξ.level 0).lineBundle := by
  let := isInvertibleModule_level ξ 0
  have : IsAffine (B.inclusion.obj (ξ.level 0).base) :=
    IsAffine.of_isIso (eqToHom (level_scheme_eq ξ 0))
  exact (Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple _ _).mp
    (ξ.level 0).relativelyAmple

end Tower

namespace Algebraization

variable {ξ}

/-- **An algebraization over the limit of the truncations.** The data in the form in which
Stacks 0D4T produces it, over `Spec (lim R ⧸ 𝔪 ^ (n + 1))` with the canonical maps from the
truncations, transported to the complete local base `Spec R`. -/
def ofLimit (X : Scheme.{u}) (f : X ⟶ Spec (limit (ringSystem ξ))) [IsProper f] [Flat f]
    (hfp : FinitePresentation f) (L : X.Modules) [IsInvertibleModule X L] (hL : IsAmple X L)
    (j : ∀ n, (ξ.level n).total ⟶ X)
    (hj : ∀ n, IsPullback (j n) (levelToTruncation ξ n) f
      (Spec.map (limit.π (ringSystem ξ) (op n))))
    (transition_j : ∀ n, (ξ.transition n).totalMap ≫ j (n + 1) = j n)
    (ψ : ∀ n, (Scheme.Modules.pullback (j n)).obj L ≅ (ξ.level n).lineBundle)
    (transition_ψ : ∀ n,
      (Scheme.Modules.pullbackComp (ξ.transition n).totalMap (j (n + 1))).symm.app L ≪≫
        (Scheme.Modules.pullback (ξ.transition n).totalMap).mapIso (ψ (n + 1)) ≪≫
          (ξ.transition n).lineBundleIso ≍ ψ n) :
    Algebraization ξ :=
  let e : CommRingCat.of ξ.base.R ≅ limit (ringSystem ξ) :=
    (ringSystemIsLimit ξ).conePointUniqueUpToIso (limit.isLimit _)
  { X := X
    toBase := f ≫ Spec.map e.hom
    proper := inferInstance
    flat := inferInstance
    finitePresentation := by
      obtain ⟨_, _, _⟩ := hfp
      exact ⟨inferInstance, inferInstance, inferInstance⟩
    L := L
    invertible := inferInstance
    relativelyAmple := (Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple _ _).mpr hL
    j := j
    isPullback := fun n => by
      refine (hj n).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (Scheme.Spec.mapIso e.op) ?_ ?_
        ?_ ?_
      · simp
      · simp
      · simp
      · simp only [Iso.refl_hom, Category.id_comp, Functor.mapIso_hom, Iso.op_hom,
          Scheme.Spec_map, Quiver.Hom.unop_op]
        exact (Spec.map_comp e.hom (limit.π (ringSystem ξ) (op n))).symm.trans
          (congrArg Spec.map
            ((ringSystemIsLimit ξ).conePointUniqueUpToIso_hom_comp (limit.isLimit _) (op n)))
    transition_j := transition_j
    ψ := ψ
    transition_ψ := transition_ψ }

end Algebraization

/-- **A formal object of `𝒫olarized` with an algebraization is effective** (Stacks 07X7). -/
theorem isEffective_of_algebraization (a : Algebraization ξ) :
    FormalObject.IsEffective B S hS (polarizedSliceProjection B hS hT)
      (polarizedProjection_isFiberedInGroupoids_unconditional.sliceAtTerminal hT) ξ :=
  FormalObject.isEffective_of_realization _ (a.realization ξ.contains_spec_base)

/-- Two isomorphisms out of the pullbacks of a module along equal morphisms are heterogeneously
equal once they agree through the identification of the two pullbacks. -/
theorem heq_of_pullbackCongr_hom_app_comp {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    {L : Y.Modules} {M : X.Modules} (α : (Scheme.Modules.pullback f).obj L ≅ M)
    (β : (Scheme.Modules.pullback g).obj L ≅ M)
    (hαβ : (Scheme.Modules.pullbackCongr h).hom.app L ≫ β.hom = α.hom) : α ≍ β := by
  subst h
  have : α = β := by
    ext1
    rw [← hαβ]
    simp [Scheme.Modules.pullbackCongr]
  rw [this]

/-- **Every formal object of `𝒫olarized` has an algebraization**, by Stacks 0D4T applied to its
levels over the inverse system `R ⧸ 𝔪 ^ (n + 1)`. -/
theorem nonempty_algebraization : Nonempty (Algebraization ξ) := by
  obtain ⟨Y, g, ℒ, hℒ, j, hj, e, hproper, hflat, hfp, hample, hpb, hiso, hcompat⟩ :=
    Stacks.PolarizedAlgebraization.exists_algebraization (ringSystem ξ)
      (surjective_ringSystem_map ξ) (ker_ringSystem_map_le_nilradical ξ)
      (fun n => (ξ.level n).total) (levelToTruncation ξ) (fun n => (ξ.transition n).totalMap)
      (isPullback_transition ξ) (fun n => (ξ.level n).lineBundle)
      (hL := fun n => isInvertibleModule_level ξ n) (fun n => (ξ.transition n).lineBundleIso)
      (hproper := fun n => isProper_levelToTruncation ξ n)
      (hflat := fun n => flat_levelToTruncation ξ n)
      (finitePresentation_levelToTruncation ξ) (isAmple_level_zero ξ)
  have := hproper
  have := hflat
  let ψ : ∀ n, (Scheme.Modules.pullback (j n)).obj ℒ ≅ (ξ.level n).lineBundle :=
    fun n => @asIso _ _ _ _ (e n) (hiso n)
  refine ⟨Algebraization.ofLimit Y g hfp ℒ hample j hpb hj ψ fun n => ?_⟩
  refine heq_of_pullbackCongr_hom_app_comp (hj n) _ _ ?_
  change (Scheme.Modules.pullbackCongr (hj n)).hom.app ℒ ≫ e n =
    (Scheme.Modules.pullbackComp _ _).inv.app ℒ ≫
      (Scheme.Modules.pullback (ξ.transition n).totalMap).map (e (n + 1)) ≫
        (ξ.transition n).lineBundleIso.hom
  rw [← hcompat n, ← Category.assoc, ← NatTrans.comp_app, Iso.inv_hom_id, NatTrans.id_app,
    Category.id_comp]

/-- **Every formal object of `𝒫olarized` over a terminal base scheme is effective.** -/
theorem isEffective : FormalObject.IsEffective B S hS (polarizedSliceProjection B hS hT)
    (polarizedProjection_isFiberedInGroupoids_unconditional.sliceAtTerminal hT) ξ :=
  isEffective_of_algebraization ξ (nonempty_algebraization ξ).some

end AlgebraicGeometry.PolarizedFormal

namespace AlgebraicGeometry

open PolarizedFormal

/-- **Stacks 0D4U.** Consider the stack `𝒫olarized` over the base scheme `Spec ℤ`. Then every
formal object (Stacks 07X4) is effective (Stacks 07X7): it is, up to isomorphism, the system of
restrictions to the infinitesimal thickenings `Spec(R / 𝔪^{n+1})` of a polarized family over its
complete local base `Spec R`. -/
@[stacks 0D4U]
theorem polarizedFormalObject_isEffective (B : BigFppfSite.{u})
    (hZ : B.Contains (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (ξ : FormalObject B _ hZ (polarizedSliceProjection B hZ (isTerminal_obj_specULiftZ B hZ))) :
    FormalObject.IsEffective B _ hZ (polarizedSliceProjection B hZ (isTerminal_obj_specULiftZ B hZ))
      (polarizedProjection_isFiberedInGroupoids_unconditional.sliceAtTerminal
        (isTerminal_obj_specULiftZ B hZ)) ξ :=
  PolarizedFormal.isEffective ξ

end AlgebraicGeometry

end
