module

public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.ComparisonWithEtale
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.AcyclicCoveringFamilyOfSize

/-!
# Pro-étale cohomology of `ε⁻¹ℐ` over limits of quasi-compact quasi-separated étale schemes

Let `X` be a scheme, let `ε : X_proétale → X_étale` be the comparison morphism of sites with
inverse image `ε⁻¹`, and let `ℐ` be an injective abelian sheaf on `X_étale`. Let `T` be an object
of `X_proétale` which is the limit, on underlying schemes, of a cofiltered system `T_a` of
quasi-compact and quasi-separated objects of `X_étale` with affine transition morphisms. Then
`H^q(T, ε⁻¹ℐ) = 0` for `q > 0`.

For affine stages this is Stacks 099U at the affine object `T`, which is ind-étale over each stage.
The general case is reached in two steps, each by the Čech criterion of Stacks 03F7 along the
covering of `T` obtained by base changing a finite affine open covering `{W_k}` of one stage
`T_{a₀}`. Its members `W_k ×_{T_{a₀}} T` and their iterated fibre products are limits of the
iterated fibre products over the later stages `T_a` of the affine schemes `W_k ×_{T_{a₀}} T_a`,
with affine transition morphisms; these are affine when `T_a` is separated, and quasi-compact
and separated when `T_a` is quasi-separated. So for separated stages the iterated fibre products
are acyclic by the affine case, and for quasi-separated stages by the separated case. The Čech
complex of `ε⁻¹ℐ` along the covering is acyclic in positive degrees in either case
(`AlgebraicGeometry.ProEtale.isZero_cechCohomology_of_isPullback`, by Stacks 099S and the
injectivity of `ℐ`).

## Main results

* `AlgebraicGeometry.ProEtale.isAffineIndEtaleOverEtale_of_isLimit`: a cofiltered limit of affine
  objects of `X_étale` is ind-étale over each of them.
* `AlgebraicGeometry.ProEtale.isZero_rightDerived_sheafSections_epsilonInverseImage_of_injective`:
  the vanishing over objects ind-étale over an affine étale `X`-scheme.
* `AlgebraicGeometry.ProEtale.isZero_rightDerived_sheafSections_epsilonInverseImage_of_isLimit`:
  the vanishing over limits of quasi-compact and quasi-separated étale `X`-schemes with affine
  transition morphisms.

## Implementation notes

Cohomology over an object `T` is the right derived functor of the sections functor `Γ(T, -)` on
abelian sheaves on `X_proétale`, the form in which Stacks 03F7 is stated, with coefficients in
abelian groups of the universe `max (u + 1) v` of `ε⁻¹`.

## References

* [Stacks Project, Tag 099U](https://stacks.math.columbia.edu/tag/099U)
* [Stacks Project, Tag 099S](https://stacks.math.columbia.edu/tag/099S)
* [Stacks Project, Tag 03F7](https://stacks.math.columbia.edu/tag/03F7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.CechSite

universe v u

namespace AlgebraicGeometry.ProEtale

attribute [local instance] isGrothendieckAbelian_sheaf_proetale enoughInjectives_sheaf_proetale

/-- Étale morphisms of schemes are stable under composition. -/
local instance : MorphismProperty.IsStableUnderComposition (@Etale : MorphismProperty Scheme.{u}) :=
  MorphismProperty.IsMultiplicative.toIsStableUnderComposition

/-- The class of étale morphisms of schemes respects isomorphisms. -/
local instance : MorphismProperty.RespectsIso (@Etale : MorphismProperty Scheme.{u}) :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso

/-- A limit cone stays a limit after restricting along `Over.forget j` and applying `F`. -/
private def isLimit_mapCone_whisker_overForget {J C D : Type*} [Category J] [Category C]
    [Category D] [IsCofiltered J] (j : J) (F : C ⥤ D) {K : J ⥤ C} (c : Cone K)
    (hc : IsLimit (F.mapCone c)) : IsLimit (F.mapCone (c.whisker (Over.forget j))) :=
  IsLimit.ofIsoLimit ((Functor.Initial.isLimitWhiskerEquiv (Over.forget j) (F.mapCone c)).symm hc)
    (Cone.ext (Iso.refl _) fun _ ↦ (Category.id_comp _).symm)

/-- **A cofiltered limit of affine objects of `X_étale` is ind-étale over each of them.** Let
`V = lim V_a` be the limit, on underlying schemes, of a cofiltered system of objects of `X_étale`
with affine underlying schemes. Then `V` is affine, and `Γ(V_{a₀}) → Γ(V)` is ind-étale for every
`a₀`: `V` is the limit of the `V_a` over `a₀`, which are affine and étale over `V_{a₀}`. -/
theorem isAffineIndEtaleOverEtale_of_isLimit (Z : Scheme.{u}) {A : Type u} [SmallCategory A]
    [IsCofiltered A] (Ub : A ⥤ Z.Etale) [∀ a, IsAffine (Ub.obj a).left]
    (c : Cone (Ub ⋙ Z.etaleToProetale))
    (hc : IsLimit ((Scheme.ProEt.forget Z ⋙ Over.forget Z).mapCone c)) :
    IsAffineIndEtaleOverEtale Z c.pt := by
  let q := Scheme.ProEt.forget Z ⋙ Over.forget Z
  have : ∀ a, IsAffine (((Ub ⋙ Z.etaleToProetale) ⋙ q).obj a) := fun a ↦
    inferInstanceAs (IsAffine (Ub.obj a).left)
  have hVa : IsAffine c.pt.left := Scheme.isAffine_of_isLimit _ hc
  obtain ⟨a₀⟩ := IsCofiltered.nonempty (C := A)
  let D : Over a₀ ⥤ Scheme.{u} := Over.forget a₀ ⋙ Ub ⋙ Z.etaleToProetale ⋙ q
  let d : D ⟶ (Functor.const (Over a₀)).obj (Ub.obj a₀).left :=
    { app b := (Ub.map b.hom).left
      naturality {b b'} g := by
        show (Ub.map g.left).left ≫ (Ub.map b'.hom).left = (Ub.map b.hom).left ≫ 𝟙 _
        rw [Category.comp_id]
        exact congrArg (fun φ ↦ φ.left) ((Ub.map_comp g.left b'.hom).symm.trans
          (congrArg Ub.map (Over.w g))) }
  let p : (Functor.const (Over a₀)).obj c.pt.left ⟶ D :=
    { app b := (c.π.app b.left).left
      naturality {b b'} g := by
        show 𝟙 _ ≫ (c.π.app b'.left).left = (c.π.app b.left).left ≫ (Ub.map g.left).left
        rw [Category.id_comp]
        exact congrArg (fun φ ↦ φ.left) (c.w g.left).symm }
  have hd (b : Over a₀) : Etale (d.app b) := by
    have h := MorphismProperty.Over.w (Ub.map b.hom)
    have : Etale ((Ub.map b.hom).left ≫ (Ub.obj a₀).hom) := by
      rw [h]; exact (Ub.obj b.left).prop
    exact MorphismProperty.of_postcomp _ _ _ (Ub.obj a₀).prop this
  have hpd (b : Over a₀) : p.app b ≫ d.app b = (c.π.app a₀).left :=
    congrArg (fun φ ↦ φ.left) (c.w b.hom)
  have hlim : IsLimit (Cone.mk c.pt.left p) :=
    isLimit_mapCone_whisker_overForget a₀ q c hc
  have : ∀ b, IsAffine (D.obj b) := fun b ↦ inferInstanceAs (IsAffine (Ub.obj b.left).left)
  refine ⟨hVa, Ub.obj a₀, c.π.app a₀, inferInstanceAs (IsAffine (Ub.obj a₀).left), ?_⟩
  have : IsAffine ((Ub ⋙ Z.etaleToProetale).obj a₀).left :=
    inferInstanceAs (IsAffine (Ub.obj a₀).left)
  have : IsAffine (((Functor.const A).obj c.pt).obj a₀).left := hVa
  exact indEtale_appTop_of_isLimit (c.π.app a₀).left D d p hd hpd hlim

/-- **The pro-étale cohomology of `ε⁻¹ℐ` vanishes over objects ind-étale over an affine étale
`X`-scheme**, for an injective abelian sheaf `ℐ` on `X_étale`, in the form of right derived
sections: this is `AlgebraicGeometry.ProEtale.subsingleton_ext_proetaleInverseImage_of_injective`
read through the identification of `Ext` out of the free sheaf on `V` with derived sections. -/
theorem isZero_rightDerived_sheafSections_epsilonInverseImage_of_injective (Z : Scheme.{u})
    (I : Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) [Injective I] {V : Z.ProEt}
    (hV : IsAffineIndEtaleOverEtale Z V) (q : ℕ) (hq : 0 < q) :
    IsZero ((((sheafSections (Scheme.ProEt.topology Z) AddCommGrpCat.{max (u + 1) v}).obj
      (op V)).rightDerived q).obj ((epsilonInverseImage.{u, v} Z).obj I)) := by
  have hsub := subsingleton_ext_proetaleInverseImage_of_injective.{max (u + 1) v}
    (epsilonAdjunction.{u, v} Z) I hV q hq
  open Stacks.Cohomology.FreeYonedaUnivLE in
  obtain ⟨e⟩ := nonempty_extFunctorObj_iso_rightDerived_sections_of_enoughInjectives.{max (u + 1) v}
    (Scheme.ProEt.topology Z) V q
  exact (@AddCommGrpCat.isZero_of_subsingleton _ hsub).of_iso (e.app _).symm

variable {X : Scheme.{u}} (I : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
  [Injective I]

/-- **The covering step.** Let `T` be the limit, on underlying schemes, of a cofiltered system
`T_a` of quasi-compact and quasi-separated objects of `X_étale` with affine transition morphisms.
Let `Q` be a property of schemes such that

* `H^q(T', ε⁻¹ℐ) = 0` for `q > 0` whenever `T'` is the limit of a cofiltered system of objects of
  `X_étale` with affine transition morphisms whose underlying schemes satisfy `Q`, and
* every iterated fibre product of affine schemes over a stage `T_a` satisfies `Q`.

Then `H^q(T, ε⁻¹ℐ) = 0` for `q > 0`. The proof is the Čech criterion of Stacks 03F7 along the
base change to `T` of a finite affine open covering of one stage. -/
theorem isZero_rightDerived_sheafSections_epsilonInverseImage_of_isLimit_of_prod
    (Q : Scheme.{u} → Prop)
    (hQ : ∀ {A' : Type u} [SmallCategory A'] [IsCofiltered A'] (Ub' : A' ⥤ X.Etale),
      (∀ {a b : A'} (f : a ⟶ b), IsAffineHom (Ub'.map f).left) → (∀ a, Q (Ub'.obj a).left) →
      ∀ {T' : X.ProEt} (πT' : (Functor.const A').obj T' ⟶ Ub' ⋙ X.etaleToProetale),
      IsLimit ((Scheme.ProEt.forget X ⋙ Over.forget X).mapCone (Cone.mk T' πT')) →
      ∀ q : ℕ, 0 < q →
        IsZero ((((sheafSections (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v}).obj
          (op T')).rightDerived q).obj ((epsilonInverseImage.{u, v} X).obj I)))
    {A : Type u} [SmallCategory A] [IsCofiltered A] (Ub : A ⥤ X.Etale)
    [∀ a, CompactSpace (Ub.obj a).left] [∀ a, QuasiSeparatedSpace (Ub.obj a).left]
    [∀ {a b : A} (f : a ⟶ b), IsAffineHom (Ub.map f).left]
    (hQprod : ∀ (a : A) (E : PreZeroHypercover.{u} ((Ub ⋙ X.etaleToProetale).obj a)),
      (∀ k, IsAffine (E.X k).left) → ∀ (n : ℕ) (t : Fin (n + 1) → E.I₀),
        Q (∏ᶜ fun i ↦ Over.mk (E.f (t i))).left.left)
    {T : X.ProEt} (πT : (Functor.const A).obj T ⟶ Ub ⋙ X.etaleToProetale)
    (hT : IsLimit ((Scheme.ProEt.forget X ⋙ Over.forget X).mapCone (Cone.mk T πT)))
    (q : ℕ) (hq : 0 < q) :
    IsZero ((((sheafSections (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v}).obj
      (op T)).rightDerived q).obj ((epsilonInverseImage.{u, v} X).obj I)) := by
  let : Category.{u} (MorphismProperty.Over (@Etale : MorphismProperty Scheme.{u}) ⊤ X) :=
    inferInstanceAs (Category X.Etale)
  let qf := Scheme.ProEt.forget X ⋙ Over.forget X
  obtain ⟨a₀⟩ := IsCofiltered.nonempty (C := A)
  let 𝒰 : (Ub.obj a₀).left.OpenCover := (Ub.obj a₀).left.affineCover.finiteSubcover
  let π₀ : T.left ⟶ (Ub.obj a₀).left := (πT.app a₀).left
  let 𝒱 : T.left.OpenCover := 𝒰.pullback₁ π₀
  have hwe (k : 𝒱.I₀) : WeaklyEtale (𝒱.f k ≫ T.hom) :=
    have : WeaklyEtale T.hom := T.prop
    inferInstance
  let V (k : 𝒱.I₀) : X.ProEt := @Scheme.ProEt.mk _ _ (𝒱.f k ≫ T.hom) (hwe k)
  let ι (k : 𝒱.I₀) : V k ⟶ T := MorphismProperty.Over.homMk (𝒱.f k) rfl trivial
  let E : PreZeroHypercover.{u} T := ⟨𝒱.I₀, V, ι⟩
  have : Finite E.I₀ := inferInstanceAs (Finite 𝒰.I₀)
  have hE : Sieve.generate E.presieve₀ ∈ Scheme.ProEt.topology X T := by
    refine Precoverage.generate_mem_toGrothendieck ?_
    show Presieve.map qf (Presieve.ofArrows V ι) ∈ Scheme.proetalePrecoverage _
    rw [Presieve.map_ofArrows]
    have : MorphismProperty.ContainsIdentities (@WeaklyEtale : MorphismProperty Scheme.{u}) :=
      ⟨fun _ ↦ inferInstance⟩
    exact Scheme.zariskiPrecoverage_le_propQCPrecoverage _ 𝒱.mem₀
  have : ∀ k : E.I₀, IsAffine (𝒰.X k) := fun k ↦ inferInstanceAs (IsAffine (Spec _))
  have : ∀ k : E.I₀, Etale (𝒰.f k) := fun k ↦
    have : IsOpenImmersion (𝒰.f k) := 𝒰.map_prop k
    inferInstance
  have hpb (k : E.I₀) : IsPullback (pullback.snd π₀ (𝒰.f k)) (E.f k).left (𝒰.f k)
      (πT.app a₀).left := (IsPullback.of_hasPullback π₀ (𝒰.f k)).flip
  refine Stacks.CechSite.AcyclicOfSize.isZero_rightDerived_of_isZero_cechCohomology.{v}
    (Scheme.ProEt.topology X) E hE _
    (fun r s d hd ↦ ?_) q (isZero_cechCohomology_of_isPullback (epsilonAdjunction.{u, v} X) I Ub
      πT hT E a₀ 𝒰.X 𝒰.f (fun k ↦ pullback.snd π₀ (𝒰.f k)) hpb q hq)
  obtain ⟨Met, met, πM, hπ, hM, hMa, hMe, hMpb⟩ :=
    exists_isLimit_baseChange_of_isPullback Ub πT hT E a₀ 𝒰.X 𝒰.f
      (fun k ↦ pullback.snd π₀ (𝒰.f k)) hpb
  let B : Over a₀ ⥤ X.ProEt := (Over.forget a₀ ⋙ Ub) ⋙ X.etaleToProetale
  let M (k : E.I₀) : Over a₀ ⥤ X.ProEt := Met k ⋙ X.etaleToProetale
  let m (k : E.I₀) : M k ⟶ B := Functor.whiskerRight (met k) X.etaleToProetale
  let πB : (Functor.const (Over a₀)).obj T ⟶ B := Functor.whiskerLeft (Over.forget a₀) πT
  have hB : IsLimit (qf.mapCone (Cone.mk T πB)) :=
    isLimit_mapCone_whisker_overForget a₀ qf (Cone.mk T πT) hT
  have : ∀ (n : ℕ) (t : Fin (n + 1) → E.I₀),
      PreservesLimit (Discrete.functor fun a ↦ Over.mk (E.f (t a))) (Over.post qf) :=
    Stacks.Sites.preservesLimit_fibreProducts_overPost qf E (fun _ _ _ ↦ inferInstance)
      (fun _ _ _ ↦ inferInstance)
  have : ∀ (j : Over a₀) (n : ℕ) (t : Fin (n + 1) → E.I₀),
      PreservesLimit (Discrete.functor fun a ↦ Over.mk ((stageFamily E B M m j).f (t a)))
        (Over.post qf) := fun j ↦
    Stacks.Sites.preservesLimit_fibreProducts_overPost qf (stageFamily E B M m j)
      (fun _ _ _ ↦ inferInstance) (fun _ _ _ ↦ inferInstance)
  let P := stageFibreProduct E B M m r s
  have hPe (j : Over a₀) : Etale (P.obj j).hom := by
    have h₁ := prop_left_hom_prod @Etale (stageFamily E B M m j) (fun k ↦ hMe k j) r s
    have h₂ : Etale (B.obj j).hom := (Ub.obj j.left).prop
    rw [← MorphismProperty.Over.w (∏ᶜ fun a ↦ Over.mk ((stageFamily E B M m j).f (s a))).hom]
    infer_instance
  let Ub' : Over a₀ ⥤ X.Etale := MorphismProperty.Comma.lift
    (P ⋙ MorphismProperty.Comma.forget _ _ _ _ _) hPe (fun _ ↦ trivial) (fun _ ↦ trivial)
  have hUb' : ∀ {a b : Over a₀} (f : a ⟶ b), IsAffineHom (Ub'.map f).left := fun {i j} f ↦
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (isPullback_map_cechProductMap qf (stageFamily E B M m i) (stageFamily E B M m j)
        (stageFamilyHomOver E B M m f) r s fun a ↦ hMpb (s a) f).flip
      (inferInstanceAs (IsAffineHom (Ub.map f.left).left))
  exact hQ Ub' hUb' (fun j ↦ hQprod j.left (stageFamily E B M m j) (fun k ↦ hMa k j) r s)
    (stageFibreProductCone E B M m πB πM hπ r s).π
    (isLimitMapConeStageFibreProductCone E B M m πB πM hπ qf hB (fun k ↦ (hM k).some) r s) d hd

/-- **Separated stages.** If `T` is the limit, on underlying schemes, of a cofiltered system of
quasi-compact and separated objects of `X_étale` with affine transition morphisms, then
`H^q(T, ε⁻¹ℐ) = 0` for `q > 0`: the iterated fibre products of affine schemes over a separated
stage are affine, so the covering step reduces this to the affine case. -/
theorem isZero_rightDerived_sheafSections_epsilonInverseImage_of_isLimit_of_isSeparated
    {A : Type u} [SmallCategory A] [IsCofiltered A] (Ub : A ⥤ X.Etale)
    [∀ a, CompactSpace (Ub.obj a).left] [∀ a, (Ub.obj a).left.IsSeparated]
    [∀ {a b : A} (f : a ⟶ b), IsAffineHom (Ub.map f).left]
    {T : X.ProEt} (πT : (Functor.const A).obj T ⟶ Ub ⋙ X.etaleToProetale)
    (hT : IsLimit ((Scheme.ProEt.forget X ⋙ Over.forget X).mapCone (Cone.mk T πT)))
    (q : ℕ) (hq : 0 < q) :
    IsZero ((((sheafSections (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v}).obj
      (op T)).rightDerived q).obj ((epsilonInverseImage.{u, v} X).obj I)) := by
  refine isZero_rightDerived_sheafSections_epsilonInverseImage_of_isLimit_of_prod I IsAffine
    (fun {_} _ _ Ub' _ hQ {_} πT' hT' q hq ↦ ?_) Ub (fun a E hE n t ↦ ?_) πT hT q hq
  · have : ∀ a, IsAffine (Ub'.obj a).left := hQ
    exact isZero_rightDerived_sheafSections_epsilonInverseImage_of_injective X I
      (isAffineIndEtaleOverEtale_of_isLimit X Ub' _ hT') q hq
  · have : ((Ub ⋙ X.etaleToProetale).obj a).left.IsSeparated :=
      inferInstanceAs (Ub.obj a).left.IsSeparated
    exact isAffine_left_prod E hE n t

/-- **The pro-étale cohomology of `ε⁻¹ℐ` vanishes over limits of quasi-compact quasi-separated
étale `X`-schemes.** Let `ℐ` be an injective abelian sheaf on `X_étale` and let `T` be the limit,
on underlying schemes, of a cofiltered system of quasi-compact and quasi-separated objects of
`X_étale` with affine transition morphisms. Then `H^q(T, ε⁻¹ℐ) = 0` for `q > 0`: the iterated
fibre products of affine schemes over a quasi-separated stage are quasi-compact and separated, so
the covering step reduces this to the separated case. -/
theorem isZero_rightDerived_sheafSections_epsilonInverseImage_of_isLimit
    {A : Type u} [SmallCategory A] [IsCofiltered A] (Ub : A ⥤ X.Etale)
    [∀ a, CompactSpace (Ub.obj a).left] [∀ a, QuasiSeparatedSpace (Ub.obj a).left]
    [∀ {a b : A} (f : a ⟶ b), IsAffineHom (Ub.map f).left]
    {T : X.ProEt} (πT : (Functor.const A).obj T ⟶ Ub ⋙ X.etaleToProetale)
    (hT : IsLimit ((Scheme.ProEt.forget X ⋙ Over.forget X).mapCone (Cone.mk T πT)))
    (q : ℕ) (hq : 0 < q) :
    IsZero ((((sheafSections (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v}).obj
      (op T)).rightDerived q).obj ((epsilonInverseImage.{u, v} X).obj I)) := by
  refine isZero_rightDerived_sheafSections_epsilonInverseImage_of_isLimit_of_prod I
    (fun S ↦ S.IsSeparated ∧ CompactSpace S) (fun {_} _ _ Ub' _ hQ {_} πT' hT' q hq ↦ ?_) Ub
    (fun a E hE n t ↦ ?_) πT hT q hq
  · have : ∀ a, (Ub'.obj a).left.IsSeparated := fun a ↦ (hQ a).1
    have : ∀ a, CompactSpace (Ub'.obj a).left := fun a ↦ (hQ a).2
    exact isZero_rightDerived_sheafSections_epsilonInverseImage_of_isLimit_of_isSeparated I Ub'
      πT' hT' q hq
  · have : QuasiSeparatedSpace ((Ub ⋙ X.etaleToProetale).obj a).left :=
      inferInstanceAs (QuasiSeparatedSpace (Ub.obj a).left)
    exact isSeparated_left_prod E hE n t

end AlgebraicGeometry.ProEtale

end
