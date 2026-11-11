module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.ConstantGroup
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSite
public import StacksFrontier.AlgebraicGeometry.Topologies.BigFppfStructureSheaf

/-!
# Sections of a finite constant group scheme over a connected base

Let `H` be a finite group and `S` a scheme. The constant group scheme `G_S` over `S` is the
disjoint union of copies of `S` indexed by `H`, the copy indexed by `h` being the image of the
section `constantSection H S h` of `G_S ⟶ S`. When `S` is nonempty and connected these are all
the sections. We apply this to `S = Spec k[x]` for a field `k`, read in a big fppf site.

## Main definitions

* `AlgebraicGeometry.constantSection`: the section of `G_S ⟶ S` given by an element of `H`.

## Main results

* `AlgebraicGeometry.isColimitCofanConstantSection`: for `H` finite, the sections exhibit
  `G_S` as the coproduct of copies of `S`.
* `AlgebraicGeometry.exists_eq_constantSection`: over a nonempty connected base every section
  of `G_S ⟶ S` is one of them.
* `AlgebraicGeometry.Space.bijective_structureSheaf_map_constantGroupSiteObject`: for
  `S = Spec k[x]`, a global function on `G_S` is the same as a function on the set of
  `S`-points of `G_S` with values in `Γ(S, 𝒪_S)`.
* `AlgebraicGeometry.Space.isAffine_constantGroupSiteObject`: `G_S` is affine.
* `AlgebraicGeometry.Space.natCard_baseTerminal_hom_constantGroupSiteObject`: `G_S` has exactly
  `|H|` points over `S`.

## References

* [Stacks Project, Tag 03YW](https://stacks.math.columbia.edu/tag/03YW)
* [Stacks Project, Tag 07DC](https://stacks.math.columbia.edu/tag/07DC)
* [Stacks Project, Tag 07DD](https://stacks.math.columbia.edu/tag/07DD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry

section Scheme

variable (H : Type v) [Small.{u} H] [Group H] (S : Scheme.{u})

/-- The section of the constant group scheme `G_S ⟶ S` which is the inclusion of the copy of
`S` indexed by `h`. -/
def constantSection (h : H) : S ⟶ (constantGroupScheme.{u} H S).X.left :=
  pullback.lift (terminal.from S ≫ Sigma.ι (fun _ : H ↦ ⊤_ Scheme.{u}) h) (𝟙 S)
    (terminal.hom_ext _ _)

/-- `constantSection H S h` is a section of the structure morphism of `G_S`. -/
@[reassoc (attr := simp)]
lemma constantSection_hom (h : H) :
    constantSection H S h ≫ (constantGroupScheme.{u} H S).X.hom = 𝟙 S :=
  pullback.lift_snd _ _ _

/-- Composed with the projection to `∐_H Spec ℤ`, `constantSection H S h` lands in the
component indexed by `h`. -/
@[reassoc (attr := simp)]
lemma constantSection_fst (h : H) :
    constantSection H S h ≫
        pullback.fst (terminal.from (constantSchemeOverIntegers.{u} H)) (terminal.from S) =
      terminal.from S ≫ Sigma.ι (fun _ : H ↦ ⊤_ Scheme.{u}) h :=
  pullback.lift_fst _ _ _

/-- The locally constant map attached to a morphism through the component indexed by `h` is
constant with value `h`. -/
lemma indexMap_terminal_from_comp (h : H) (x : S) :
    indexMap H (terminal.from S ≫ Sigma.ι (fun _ : H ↦ ⊤_ Scheme.{u}) h) x = h :=
  indexMap_component H h _

/-- Two morphisms into `∐_H Spec ℤ` with the same locally constant index map agree. -/
lemma eq_of_indexMap_eq {T : Scheme.{u}} (A B : T ⟶ constantSchemeOverIntegers.{u} H)
    (e : indexMap H A = indexMap H B) : A = B :=
  calc A = ofIndexMap H (indexMap H A) := (ofIndexMap_indexMap H A).symm
    _ = ofIndexMap H (indexMap H B) := by rw [e]
    _ = B := ofIndexMap_indexMap H B

/-- Distinct elements of `H` give distinct sections over a nonempty base. -/
lemma constantSection_injective [Nonempty S] : Function.Injective (constantSection H S) := by
  intro h h' e
  obtain ⟨x⟩ : Nonempty S := inferInstance
  have key : terminal.from S ≫ Sigma.ι (fun _ : H ↦ ⊤_ Scheme.{u}) h =
      terminal.from S ≫ Sigma.ι (fun _ : H ↦ ⊤_ Scheme.{u}) h' :=
    (constantSection_fst H S h).symm.trans
      ((congrArg (· ≫ pullback.fst _ _) e).trans (constantSection_fst H S h'))
  have := congrArg (fun m ↦ indexMap H m x) key
  rwa [indexMap_terminal_from_comp, indexMap_terminal_from_comp] at this

/-- Over a nonempty connected base, every section of `G_S ⟶ S` is `constantSection H S h` for
some `h`. -/
lemma exists_eq_constantSection [PreconnectedSpace S] [Nonempty S]
    (s : S ⟶ (constantGroupScheme.{u} H S).X.left)
    (hs : s ≫ (constantGroupScheme.{u} H S).X.hom = 𝟙 S) :
    ∃ h, s = constantSection H S h := by
  obtain ⟨x⟩ : Nonempty S := inferInstance
  have hF : s ≫ pullback.fst (terminal.from (constantSchemeOverIntegers.{u} H))
        (terminal.from S) =
      terminal.from S ≫ Sigma.ι (fun _ : H ↦ ⊤_ Scheme.{u}) (indexMap H (s ≫
        pullback.fst (terminal.from (constantSchemeOverIntegers.{u} H)) (terminal.from S)) x) :=
    eq_of_indexMap_eq H _ _ (LocallyConstant.ext fun y ↦ by
      rw [indexMap_terminal_from_comp]
      exact (indexMap H _).isLocallyConstant.apply_eq_of_preconnectedSpace y x)
  exact ⟨_, pullback.hom_ext (hF.trans (constantSection_fst H S _).symm)
    (hs.trans (constantSection_hom H S _).symm)⟩

/-- For `H` finite, the sections `constantSection H S h` exhibit `G_S` as the coproduct of
copies of `S` indexed by `H`: coproducts of schemes are universal. -/
def isColimitCofanConstantSection [Finite H] :
    IsColimit (Cofan.mk (constantGroupScheme.{u} H S).X.left (constantSection H S)) :=
  Nonempty.some <|
    (FinitaryPreExtensive.isUniversal_finiteCoproducts
        (coproductIsCoproduct (fun _ : H ↦ ⊤_ Scheme.{u}))).nonempty_isColimit_of_isPullback_left
      (fun _ ↦ 𝟙 (⊤_ Scheme.{u})) (terminal.from _) (terminal.from S)
      (fun _ ↦ 𝟙 S) (fun _ ↦ terminal.from S)
      (fun _ ↦ IsPullback.of_horiz_isIso ⟨by simp⟩)
      (IsPullback.of_hasPullback (terminal.from (constantSchemeOverIntegers.{u} H))
        (terminal.from S)).flip
      _ (Iso.refl _) (fun _ ↦ terminal.hom_ext _ _)
      (fun h ↦ (congrArg (constantSection H S h ≫ ·) (Category.id_comp _)).trans
        (constantSection_hom H S h))
      (fun h ↦ (congrArg (constantSection H S h ≫ ·) (Category.id_comp _)).trans
        (constantSection_fst H S h))

/-- For `H` finite, a global function on `G_S` is determined by, and can be prescribed through,
its pullbacks along the sections `constantSection H S h`. -/
theorem bijective_Γ_map_constantSection [Finite H] :
    Function.Bijective (fun (s : Γ((constantGroupScheme.{u} H S).X.left, ⊤)) (h : H) ↦
      Scheme.Γ.map (constantSection H S h).op s) := by
  have hd := isColimitCofanConstantSection H S
  let e {X : Scheme.{u}} := AffineSpace.toSpecMvPolyIntEquiv PUnit.{u + 1} (X := X)
  have comp {X Y : Scheme.{u}} (f : X ⟶ Y)
      (m : Y ⟶ Spec (.of (MvPolynomial PUnit.{u + 1} (ULift.{u} ℤ)))) :
      e (f ≫ m) PUnit.unit = Scheme.Γ.map f.op (e m PUnit.unit) := by
    rw [Scheme.Γ_map]
    exact AffineSpace.toSpecMvPolyIntEquiv_comp _ f m _
  refine ⟨fun s t hst ↦ ?_, fun g ↦ ?_⟩
  · have key : e.symm (fun _ ↦ s) = e.symm (fun _ ↦ t) :=
      Cofan.IsColimit.hom_ext hd _ _ fun h ↦ e.injective (funext fun _ ↦ by
        change e (constantSection H S h ≫ _) PUnit.unit = e (constantSection H S h ≫ _) PUnit.unit
        rw [comp, comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
        exact congrFun hst h)
    simpa using congrFun (congrArg e key) PUnit.unit
  · refine ⟨e (Cofan.IsColimit.desc hd fun h ↦ e.symm fun _ ↦ g h) PUnit.unit,
      funext fun h ↦ ?_⟩
    refine (comp (constantSection H S h) _).symm.trans ?_
    rw [show constantSection H S h ≫ Cofan.IsColimit.desc hd (fun h ↦ e.symm fun _ ↦ g h) =
      e.symm fun _ ↦ g h from Cofan.IsColimit.fac hd _ h]
    exact congrFun (e.apply_symm_apply _) PUnit.unit

/-- For `H` finite and `S` affine, the constant group scheme `G_S` is affine. -/
theorem isAffine_constantGroupScheme [Finite H] [IsAffine S] :
    IsAffine (constantGroupScheme.{u} H S).X.left :=
  IsAffine.of_isIso (Y := ∐ fun _ : H ↦ S)
    ((isColimitCofanConstantSection H S).coconePointUniqueUpToIso
      (coproductIsCoproduct (fun _ : H ↦ S))).hom

end Scheme

namespace Space

variable {k : Type u} [Field k] (𝒞 : BigFppfSite.{u})
  (hS : 𝒞.Contains (Spec (.of (Polynomial k))))
  (H : Type v) [Small.{u} H] [Group H] [Finite H]
  (hH : 𝒞.Contains (constantGroupScheme.{u} H (Spec (.of (Polynomial k)))).X.left)

/-- The point of `G_S` over `S` given by an element of `H`, read in the big fppf site. -/
def constantGroupSitePoint (h : H) :
    baseTerminal 𝒞 _ hS ⟶ constantGroupSiteObject 𝒞 _ hS H hH :=
  Over.homMk (ObjectProperty.homMk (constantSection H _ h)) (by
    ext1
    exact constantSection_hom H _ h)

omit [Finite H] in
/-- The points of `G_S` over `S` are exactly the elements of `H`. -/
lemma bijective_constantGroupSitePoint :
    Function.Bijective (constantGroupSitePoint 𝒞 hS H hH) := by
  refine ⟨fun h h' e ↦ constantSection_injective H (Spec (.of (Polynomial k))) ?_, fun b ↦ ?_⟩
  · exact congrArg (fun b : baseTerminal 𝒞 _ hS ⟶ constantGroupSiteObject 𝒞 _ hS H hH ↦
      b.left.hom) e
  · obtain ⟨h, hh⟩ := exists_eq_constantSection H (Spec (.of (Polynomial k))) b.left.hom
      (congrArg (fun f ↦ f.hom) (Over.w b))
    refine ⟨h, ?_⟩
    ext1
    exact ObjectProperty.hom_ext _ hh.symm

/-- The equivalence between `H` and the points of `G_S` over `S`. -/
def constantGroupSitePointEquiv :
    H ≃ (baseTerminal 𝒞 _ hS ⟶ constantGroupSiteObject 𝒞 _ hS H hH) :=
  Equiv.ofBijective _ (bijective_constantGroupSitePoint 𝒞 hS H hH)

/-- Γ(G_S, 𝒪) is the ring of functions on the S-points (sections of G_S over S), S = Spec k[x]
connected. -/
theorem bijective_structureSheaf_map_constantGroupSiteObject :
    Function.Bijective (fun (s : ↥((BigFppfOver.structureSheaf 𝒞 _ hS).obj.obj
        (op (constantGroupSiteObject 𝒞 _ hS H hH))))
      (b : baseTerminal 𝒞 _ hS ⟶ constantGroupSiteObject 𝒞 _ hS H hH) =>
        (BigFppfOver.structureSheaf 𝒞 _ hS).obj.map b.op s) := by
  let e := constantGroupSitePointEquiv 𝒞 hS H hH
  have key : (fun (s : ↥((BigFppfOver.structureSheaf 𝒞 _ hS).obj.obj
        (op (constantGroupSiteObject 𝒞 _ hS H hH))))
      (b : baseTerminal 𝒞 _ hS ⟶ constantGroupSiteObject 𝒞 _ hS H hH) =>
        (BigFppfOver.structureSheaf 𝒞 _ hS).obj.map b.op s) =
      (Equiv.arrowCongr e (Equiv.refl _)) ∘
        (fun (s : Γ((constantGroupScheme.{u} H (Spec (.of (Polynomial k)))).X.left, ⊤))
          (h : H) ↦ Scheme.Γ.map (constantSection H _ h).op s) := by
    funext s b
    conv_lhs => rw [← e.apply_symm_apply b]
    rfl
  rw [key]
  exact (Equiv.bijective _).comp (bijective_Γ_map_constantSection H _)

/-- The constant group scheme `G_S` over `S = Spec k[x]` is affine. -/
theorem isAffine_constantGroupSiteObject :
    IsAffine ((BigFppfOver.toScheme 𝒞 _ hS).obj (constantGroupSiteObject 𝒞 _ hS H hH)) :=
  isAffine_constantGroupScheme H _

omit [Finite H] in
/-- The constant group scheme `G_S` over `S = Spec k[x]` has exactly `|H|` points over `S`.
This holds for any `H`, finite or not. -/
theorem natCard_baseTerminal_hom_constantGroupSiteObject :
    Nat.card (baseTerminal 𝒞 _ hS ⟶ constantGroupSiteObject 𝒞 _ hS H hH) = Nat.card H :=
  (Nat.card_congr (constantGroupSitePointEquiv 𝒞 hS H hH)).symm

end Space

end AlgebraicGeometry
