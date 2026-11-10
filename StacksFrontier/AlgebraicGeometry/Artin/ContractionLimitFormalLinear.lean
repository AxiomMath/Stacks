module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitTowerRingMap
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitAuxOverS

/-!
# The ring map of a morphism to `Spf B` is linear over an open of the base

Let `O ⊆ S` be an affine open with `R = Γ(O, 𝒪)` and let `ρ : R ⟶ B` be a ring map through which
every quotient stage `Spec (B ⧸ J) ⟶ S` factors as `Spec (B ⧸ J) ⟶ Spec R ≅ O ⊆ S`. For a
quasi-compact algebraic space `X` mapping to an object `V` of the site lying over `O`, the ring map
`B ⟶ Γ(X, 𝒪)` of any morphism `X ⟶ Spf B` is `R`-linear: everything lies over `S`, and maps into
the open `O` of `S` are unique. In the proof of Stacks 0GI5 this makes the ring map
`ψ : B ⟶ C_k^∧` of the lifted formal component an `R`-algebra map.

## Main results

* `AlgebraicGeometry.Artin.FormalRing.formalRingHom_ρ`: the `R`-linearity.
* `AlgebraicGeometry.Artin.FormalRing.towerRingHom_ρ`: the same for the tower ring.

## References

* [Stacks Project, Tag 0GI5](https://stacks.math.columbia.edu/tag/0GI5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Topology

universe u

namespace AlgebraicGeometry.Artin.FormalRing

open Space FormalSpace FormalDictionary

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance]
  AlgebraicGeometry.Artin.FormalDictionary.instTopologicalSpaceAdicCompletion

/-- **Maps into an open of the base are unique.** -/
theorem hom_ext_yoneda_openObj (O : S.Opens) (hOC : B.Contains (O : Scheme.{u}))
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a b : F ⟶ yoneda.obj (openObj hS O hOC)) : a = b := by
  ext T x
  refine BigFppfOver.map_toScheme_injective B S hS ?_
  have h (c : F ⟶ yoneda.obj (openObj hS O hOC)) :
      (BigFppfOver.toScheme B S hS).map (c.app T x) ≫ O.ι = T.unop.hom.hom :=
    congrArg (fun k => k.hom) (Over.w (c.app T x))
  exact (cancel_mono O.ι).1 ((h a).trans (h b).symm)

variable (O : S.Opens) [IsAffine (O : Scheme.{u})] (hOC : B.Contains (O : Scheme.{u}))
  {Bt : Type u} [CommRing Bt] [TopologicalSpace Bt] [IsTopologicalRing Bt]
  [IsLinearTopology Bt Bt] (hB : TopologicalRing.IsWeaklyAdmissible Bt)
  {DB : QuotientSystem B S hS Bt}
  (ρ : Γ((O : Scheme.{u}), ⊤) →+* Bt)
  (hρ : ∀ J : { J : Ideal Bt // TopologicalRing.IsWeakIdealOfDefinition J },
    DB.overS J = Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk J.1).comp ρ)) ≫
      (O : Scheme.{u}).isoSpec.inv ≫ O.ι)

/-- The morphism `Spec (B ⧸ J) ⟶ O` of a quotient stage. -/
def stageToOpen (J : WeakIdeals Bt) : stageObj DB J ⟶ openObj hS O hOC :=
  FormalSpace.siteHom B S hS
    (Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk (OrderDual.ofDual J).1).comp ρ)) ≫
      (O : Scheme.{u}).isoSpec.inv) (by
    change _ ≫ O.ι = DB.overS (OrderDual.ofDual J)
    rw [hρ]
    exact Category.assoc _ _ _)

omit [IsTopologicalRing Bt] [IsLinearTopology Bt Bt] in
/-- On global sections, the morphism `stageToOpen` sends `r ∈ Γ(O, ⊤)` to the image of `ρ r` in
`B ⧸ J`. -/
theorem appTop_stageToOpen (J : WeakIdeals Bt) (r : Γ((O : Scheme.{u}), ⊤)) :
    ((BigFppfOver.toScheme B S hS).map (stageToOpen O hOC ρ hρ J)).appTop.hom r =
      stageRingHom DB J (ρ r) := by
  change ((Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk (OrderDual.ofDual J).1).comp ρ)) ≫
    (O : Scheme.{u}).isoSpec.inv).appTop).hom r = _
  have hiso :
      (O : Scheme.{u}).isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ((O : Scheme.{u}), ⊤)).inv := by
    rw [← cancel_mono (Scheme.ΓSpecIso Γ((O : Scheme.{u}), ⊤)).hom, Iso.inv_hom_id,
      ← Scheme.toSpecΓ_appTop, ← Scheme.isoSpec_hom, ← Scheme.Hom.comp_appTop, Iso.hom_inv_id]
    rfl
  rw [Scheme.Hom.comp_appTop, hiso, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

/-- `V ⟶ O` as a morphism of the site. -/
def toOpen {V : BigFppfOver B S hS} (f : (BigFppfOver.toScheme B S hS).obj V ⟶ (O : Scheme.{u}))
    (hf : f ≫ O.ι = V.hom.hom) : V ⟶ openObj hS O hOC :=
  FormalSpace.siteHom B S hS f hf

include hρ hOC in
/-- **The ring map of a morphism to `Spf B` is `R`-linear.** -/
theorem formalRingHom_ρ {X : AlgebraicSpaces B S hS} (hX : IsQuasiCompactSpace B S hS X.1)
    (F : sheafifiedULift B S hS X.1 ⟶ formalSpectrum DB) {V : BigFppfOver B S hS}
    (g : X.1 ⟶ yoneda.obj V) (f : (BigFppfOver.toScheme B S hS).obj V ⟶ (O : Scheme.{u}))
    (hf : f ≫ O.ι = V.hom.hom) (r : Γ((O : Scheme.{u}), ⊤)) :
    formalRingHom hB X hX F (ρ r) =
      pullbackRingHom B V (ObjectProperty.homMk g) (f.appTop.hom r) := by
  obtain ⟨J, t, ht⟩ := exists_isStageFactor hB X hX F
  rw [formalRingHom_eq hB X hX ht]
  change pullbackRingHom B (stageObj DB J) (ObjectProperty.homMk t) (stageRingHom DB J (ρ r)) = _
  rw [← appTop_stageToOpen O hOC ρ hρ J r]
  refine (pullbackRingHom_homMk_comp X t (stageToOpen O hOC ρ hρ J) r).symm.trans ?_
  have e := hom_ext_yoneda_openObj O hOC (t ≫ yoneda.map (stageToOpen O hOC ρ hρ J))
    (g ≫ yoneda.map (toOpen O hOC f hf))
  exact (congrArg (fun m => pullbackRingHom B (openObj hS O hOC)
    (ObjectProperty.homMk m : X ⟶ schemeSpace (openObj hS O hOC)) r) e).trans
      (pullbackRingHom_homMk_comp X g (toOpen O hOC f hf) r)

variable {V : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)]
  {I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)}
  {X : AlgebraicSpaces B S hS} (g : X.1 ⟶ yoneda.obj V)
  {Z : Set (Space.points B S hS (yoneda.obj V))}
  (hZI : ∀ x, x ∈ Z ↔ Space.pointsToScheme B S hS V x ∈
    ((BigFppfOver.toScheme B S hS).obj V).zeroLocus
      (I : Set Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))
  (hqc : ∀ n, IsQuasiCompactSpace B S hS (fibreSpace V I (spaceHom V g) n).1)

include hρ hOC in
/-- **The ring map `ψ_F` of the tower ring is `R`-linear.** -/
theorem towerRingHom_ρ (F : completionSheaf B S hS X.1 (pointsMap B S hS X.1 g ⁻¹' Z) ⟶
      formalSpectrum DB) (f : (BigFppfOver.toScheme B S hS).obj V ⟶ (O : Scheme.{u}))
    (hf : f ≫ O.ι = V.hom.hom) (r : Γ((O : Scheme.{u}), ⊤)) :
    towerRingHom g hZI hqc hB F (ρ r) =
      towerOf I g (pullbackRingHom B V (spaceHom V g) (f.appTop.hom r)) := by
  refine Subtype.ext (funext fun n => ?_)
  change formalRingHom hB _ (hqc (n + 1)) _ (ρ r) =
    globalSectionsRingHomSite B S hS (fibreInclusion V I (spaceHom V g) (n + 1))
      (pullbackRingHom B V (spaceHom V g) (f.appTop.hom r))
  rw [formalRingHom_ρ O hOC hB ρ hρ (hqc (n + 1)) _
    ((fibreInclusion V I (spaceHom V g) (n + 1)).hom ≫ g) f hf r]
  exact (congrArg (fun φ => φ (f.appTop.hom r)) (globalSectionsRingHomSite_comp_pullbackRingHom
    (V := V) (fibreInclusion V I (spaceHom V g) (n + 1)) (spaceHom V g))).symm

end AlgebraicGeometry.Artin.FormalRing

end
