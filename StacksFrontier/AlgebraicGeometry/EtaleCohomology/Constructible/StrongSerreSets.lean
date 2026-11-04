module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Yoneda
public import Mathlib.CategoryTheory.RegularCategory.Basic
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.PreservesLimits
public import Mathlib.CategoryTheory.Sites.RegularEpi
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Etale.SmallEtalePostcompose
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLimitsSets
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ConstructibleQuasiCompact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ShriekGeneratorConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SubterminalSheaves
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.Comparison
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.Defs
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.LocallySurjectiveTransfer
import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits

/-!
# Subsheaves and quotient sheaves of a constructible sheaf of sets

Let `X` be a Noetherian scheme. A subsheaf and a quotient sheaf of a constructible sheaf of sets
on the small étale site of `X` are constructible. This is part (1) of Stacks 09BH.

The route is not the Noetherian induction of the source but the presentation by representables:
a constructible sheaf is covered by a finite coproduct of sheaves `h_U` with `U` quasi-compact,
a subobject of `h_U` is itself representable — by an open subscheme, since a subobject of a
representable sheaf is subterminal over `U` and Stacks 04HV identifies subterminal sheaves with
opens — and an open of a Noetherian scheme is quasi-compact, so Stacks 03S8 makes that subobject
constructible. Closure under finite limits and colimits, Stacks 03RZ (1), then transports the
conclusion from the cover to an arbitrary subobject, and from subobjects to quotients by the
source's own argument: a quotient of `ℱ` is the coequalizer of the kernel pair
`ℱ ×_𝒬 ℱ ⊆ ℱ × ℱ`.

## Main results

* `AlgebraicGeometry.representableIsConstructibleSetSheaf`: **Stacks 03S8 (1)** on a Noetherian
  scheme, in the form the statements below consume.
* `AlgebraicGeometry.hasFiniteRepresentableCover`: the surjection half of **Stacks 09Y9** on a
  Noetherian scheme, in the form the statements below consume.
* `AlgebraicGeometry.isConstructibleSetSheaf_of_mono`: a subsheaf of a constructible sheaf of
  sets is constructible.
* `AlgebraicGeometry.isConstructibleSetSheaf_of_epi`: a quotient sheaf of a constructible sheaf
  of sets is constructible.

## Implementation notes

The two statements of Stacks 09BH (1) name their two inputs `hrep` and `hcover`, and the library
proves both of them on a Noetherian scheme, so neither input has to be found elsewhere.

Stacks 03S8 is `AlgebraicGeometry.representableIsConstructibleSetSheaf`, which is
`AlgebraicGeometry.isConstructibleSetSheaf_sheafifiedYoneda_of_qcqs` with its quasi-compactness
and quasi-separatedness side conditions on `X` read off from `IsNoetherian X.obj`.

The surjection half of Stacks 09Y9 is `AlgebraicGeometry.hasFiniteRepresentableCover`, which is
`AlgebraicGeometry.exists_finite_representable_epi_of_isConstructibleSetSheaf` of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Constructible/ConstructibleQuasiCompact.lean`
with the same two side conditions supplied. That statement does not pass through Stacks 03RV and
so needs no descent input: quasi-compactness of a constructible sheaf is checked after inverse
image along a finite jointly surjective family, and such a family is obtained by refining, inside
each stratum of a constructible stratification, the covering on which the sheaf becomes finite
constant to one by finitely many affine objects.

A subobject of a representable sheaf is handled through the localization of the small étale site
at the representing object, `AlgebraicGeometry.SmallEtale.localizationEquivalence`: a monomorphism
into `h_U` is the same as a subterminal sheaf on the slice at `U`, and transporting it along that
equivalence turns Stacks 04HV on `U` into the statement that the subobject is represented by an
open of `U`.

## References

* [Stacks Project, Tag 09BH](https://stacks.math.columbia.edu/tag/09BH)
* [Stacks Project, Tag 03RZ](https://stacks.math.columbia.edu/tag/03RZ)
* [Stacks Project, Tag 03S8](https://stacks.math.columbia.edu/tag/03S8)
* [Stacks Project, Tag 04HV](https://stacks.math.columbia.edu/tag/04HV)
* [Stacks Project, Tag 09Y9](https://stacks.math.columbia.edu/tag/09Y9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w t

namespace AlgebraicGeometry

/-- A binary product of constructible sheaves of sets is constructible. -/
public theorem isConstructibleSetSheaf_prod
    (B : BigEtaleSite.{u}) (X : B.Scheme)
    {F G : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))}
    (hF : IsConstructibleSetSheaf B X F)
    (hG : IsConstructibleSetSheaf B X G) :
    IsConstructibleSetSheaf B X (F ⨯ G) :=
  isConstructibleSetSheaf_limit B X (pair F G) (by
    rintro ⟨_ | _⟩
    · simpa using hF
    · simpa using hG)

private theorem isColimit_pullback_coproduct
    {C : Type*} [Category C] [HasPullbacks C] [FinitaryPreExtensive C]
    {I : Type*} [Finite I] (A : I → C) [HasCoproduct A]
    {G : C} (i : G ⟶ ∐ A) :
    Nonempty (IsColimit (Cofan.mk G (fun j => pullback.snd (Sigma.ι A j) i))) := by
  refine (FinitaryPreExtensive.isUniversal_finiteCoproducts
    (coproductIsCoproduct A)).nonempty_isColimit_of_isPullback_right (p₁ := i) (p₂ := 𝟙 G)
    (Sigma.ι A) (𝟙 _) i
    (fun j => pullback.fst (Sigma.ι A j) i)
    (fun j => pullback.snd (Sigma.ι A j) i)
    (fun j => IsPullback.of_hasPullback _ _)
    (IsPullback.of_vert_isIso ⟨by simp⟩)
    (Cofan.mk G (fun j => pullback.snd (Sigma.ι A j) i)) (Iso.refl _) (fun j => by simp)
    (fun j => by simpa using (pullback.condition (f := Sigma.ι A j) (g := i)).symm)
    (fun j => by simp)

/-- The category of sheaves of sets on the small étale site of `X` has finite colimits. -/
local instance (B : BigEtaleSite.{u}) (X : B.Scheme) :
    HasFiniteColimits (Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))) :=
  CategoryTheory.Sheaf.instHasFiniteColimits

/-- The small étale site of `X` has finite limits. -/
local instance (B : BigEtaleSite.{u}) (X : B.Scheme) :
    HasFiniteLimits (SmallEtale B X.obj X.property) :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

/-- The category of sheaves of sets on the small étale site of `X` has coproducts indexed by a
finite type. -/
local instance (B : BigEtaleSite.{u}) (X : B.Scheme) {I : Type} [Finite I] :
    HasColimitsOfShape (Discrete I)
      (Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))) := by
  let := Fintype.ofFinite I
  exact HasFiniteColimits.out _

/-- `RepresentableIsConstructibleSetSheaf B X` is Stacks 03S8 on `X`: the sheaf represented by a
quasi-compact quasi-separated object of the small étale site of `X` is constructible. -/
public abbrev RepresentableIsConstructibleSetSheaf (B : BigEtaleSite.{u}) (X : B.Scheme) : Prop :=
  ∀ W : SmallEtale B X.obj X.property,
    CompactSpace ((SmallEtale.toScheme B X.obj X.property).obj W) →
    QuasiSeparatedSpace ((SmallEtale.toScheme B X.obj X.property).obj W) →
    IsConstructibleSetSheaf B X
      ((Sheaf.sheafifiedYoneda (SmallEtale.topology B X.obj X.property)).obj W)

/-- **Stacks 03S8, part (1), on a Noetherian scheme.** The sheaf of sets represented by a
quasi-compact quasi-separated object of the small étale site of a Noetherian scheme is
constructible.

This is `AlgebraicGeometry.isConstructibleSetSheaf_sheafifiedYoneda_of_qcqs` with its
quasi-compactness and quasi-separatedness hypotheses on `X` supplied from `IsNoetherian X.obj`,
which is the form in which the statements below consume it: on a Noetherian scheme this input of
Stacks 09BH (1) is a theorem rather than an assumption. -/
@[sga "4 IX 2.7.1" "Sufficiency"]
public theorem representableIsConstructibleSetSheaf (B : BigEtaleSite.{u}) (X : B.Scheme)
    [IsNoetherian X.obj] : RepresentableIsConstructibleSetSheaf B X := by
  obtain ⟨_, _⟩ := (isNoetherian_iff X.obj).mp ‹_›
  have : QuasiSeparatedSpace X.obj := IsLocallyNoetherian.quasiSeparatedSpace
  intro W (_ : CompactSpace W.obj.left.obj) (_ : QuasiSeparatedSpace W.obj.left.obj)
  exact isConstructibleSetSheaf_sheafifiedYoneda_of_qcqs B X W

/-- `HasFiniteRepresentableCover B X` is the surjection half of Stacks 09Y9 on `X`: every
constructible sheaf of sets on the small étale site of `X` receives an epimorphism from a finite
coproduct of sheaves represented by quasi-compact quasi-separated objects. -/
public abbrev HasFiniteRepresentableCover (B : BigEtaleSite.{u}) (X : B.Scheme) : Prop :=
  ∀ F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1)),
    IsConstructibleSetSheaf B X F →
    ∃ (n : ℕ) (U : Fin n → SmallEtale B X.obj X.property),
      (∀ i, CompactSpace ((SmallEtale.toScheme B X.obj X.property).obj (U i)) ∧
        QuasiSeparatedSpace ((SmallEtale.toScheme B X.obj X.property).obj (U i))) ∧
      ∃ p : (∐ fun i ↦ (Sheaf.sheafifiedYoneda
        (SmallEtale.topology B X.obj X.property)).obj (U i)) ⟶ F, Epi p

/-- **Stacks 09Y9, the surjection half, on a Noetherian scheme.** Every constructible sheaf of
sets on the small étale site of a Noetherian scheme receives an epimorphism from a finite
coproduct of sheaves represented by quasi-compact quasi-separated objects.

This is `AlgebraicGeometry.exists_finite_representable_epi_of_isConstructibleSetSheaf` with its
quasi-compactness and quasi-separatedness hypotheses on `X` supplied from `IsNoetherian X.obj`,
which is the form in which the statements below consume it: on a Noetherian scheme this input of
Stacks 09BH (1) is a theorem rather than an assumption. -/
public theorem hasFiniteRepresentableCover (B : BigEtaleSite.{u}) (X : B.Scheme)
    [IsNoetherian X.obj] : HasFiniteRepresentableCover B X := by
  obtain ⟨_, _⟩ := (isNoetherian_iff X.obj).mp ‹_›
  have : QuasiSeparatedSpace X.obj := IsLocallyNoetherian.quasiSeparatedSpace
  exact fun F hF => exists_finite_representable_epi_of_isConstructibleSetSheaf B X F hF

/-- The sheaf represented by a product of two objects of the small étale site is the product of
the two represented sheaves: sheafified Yoneda preserves finite limits. -/
private def sheafifiedYonedaProductIso
    (B : BigEtaleSite.{u}) (X : B.Scheme)
    (U V : SmallEtale B X.obj X.property) :
    ((Sheaf.sheafifiedYoneda (SmallEtale.topology B X.obj X.property)).obj U) ⨯
      ((Sheaf.sheafifiedYoneda (SmallEtale.topology B X.obj X.property)).obj V) ≅
      (Sheaf.sheafifiedYoneda (SmallEtale.topology B X.obj X.property)).obj (U ⨯ V) := by
  let J := SmallEtale.topology B X.obj X.property
  let H := Sheaf.sheafifiedYoneda J
  have : PreservesFiniteLimits H := by
    change PreservesFiniteLimits (uliftYoneda.{u + 1} ⋙ presheafToSheaf J (Type (u + 1)))
    infer_instance
  exact (PreservesLimitPair.iso H U V).symm

/-- The product of two finite coproducts is the coproduct of the pairwise products. -/
private def finiteCoproductProductIso
    {C : Type*} [Category C] [HasFiniteLimits C] [HasFiniteColimits C]
    [FinitaryPreExtensive C]
    {I J : Type} [Finite I] [Finite J] (A : I → C) (D : J → C) :
    (∐ A) ⨯ (∐ D) ≅ ∐ fun p : I × J => A p.1 ⨯ D p.2 := by
  let := Fintype.ofFinite I
  let := Fintype.ofFinite J
  let : HasPullbacks C := HasFiniteLimits.out _
  let : HasColimitsOfShape (Discrete I) C := HasFiniteColimits.out _
  let : HasColimitsOfShape (Discrete J) C := HasFiniteColimits.out _
  let : HasColimitsOfShape (Discrete (I × J)) C := HasFiniteColimits.out _
  let f : ∀ i, A i ⟶ ⊤_ C := fun _ => terminal.from _
  let g : ∀ j, D j ⟶ ⊤_ C := fun _ => terminal.from _
  let h := FinitaryPreExtensive.isIso_sigmaDesc_map f g
  let : HasLimitsOfShape WalkingCospan C := HasFiniteLimits.out WalkingCospan
  let : HasLimit (cospan (Sigma.desc f) (Sigma.desc g)) :=
    HasLimitsOfShape.has_limit _
  let e₁ : (∐ A) ⨯ (∐ D) ≅ pullback (Sigma.desc f) (Sigma.desc g) :=
    prodIsoPullback _ _ ≪≫ pullback.congrHom (Subsingleton.elim _ _) (Subsingleton.elim _ _)
  let e₂ : (∐ fun p : I × J => A p.1 ⨯ D p.2) ≅
      (∐ fun p : I × J => pullback (f p.1) (g p.2)) :=
    HasColimit.isoOfNatIso (Discrete.natIso
      (fun p : Discrete (I × J) => prodIsoPullback (A p.as.1) (D p.as.2)))
  exact e₁ ≪≫ (asIso (Sigma.desc fun (p : I × J) =>
      pullback.map (f p.1) (g p.2) (Sigma.desc f) (Sigma.desc g)
        (Sigma.ι _ p.1) (Sigma.ι _ p.2) (𝟙 _) (by simp) (by simp))).symm ≪≫ e₂.symm

/-- If every subobject of every member of a finite family is constructible, then so is every
subobject of their coproduct: the coproduct decomposition is universal, so the subobject is the
coproduct of its intersections with the members. -/
private theorem isConstructibleSetSheaf_of_mono_coproduct
    (B : BigEtaleSite.{u}) (X : B.Scheme)
    {I : Type} [Finite I]
    (A : I → Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1)))
    (hA : ∀ j, ∀ {H : Sheaf (SmallEtale.topology B X.obj X.property)
      (Type (u + 1))} (m : H ⟶ A j), [Mono m] → IsConstructibleSetSheaf B X H)
    {G : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))}
    (i : G ⟶ ∐ A) [Mono i] : IsConstructibleSetSheaf B X G := by
  let := Fintype.ofFinite I
  let P := fun j => pullback (Sigma.ι A j) i
  obtain ⟨hc⟩ := isColimit_pullback_coproduct A i
  exact isConstructibleSetSheaf_congr B X
    ((coproductIsCoproduct P).coconePointUniqueUpToIso hc)
    (isConstructibleSetSheaf_colimit B X (Discrete.functor P)
      fun j => hA j.as (pullback.fst (Sigma.ι A j.as) i))

/-- An epimorphic image of a constructible sheaf of sets whose kernel pair is constructible is
constructible: in a sheaf topos an epimorphism is the coequalizer of its kernel pair, and
constructible sheaves of sets are closed under finite colimits. -/
private theorem isConstructibleSetSheaf_of_epi_of_kernelPair
    (B : BigEtaleSite.{u}) (X : B.Scheme)
    {P G : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))}
    (q : P ⟶ G) [Epi q]
    (hP : IsConstructibleSetSheaf B X P)
    (hR : IsConstructibleSetSheaf B X (pullback q q)) :
    IsConstructibleSetSheaf B X G := by
  let D := parallelPair (pullback.fst q q) (pullback.snd q q)
  have hD : ∀ j, IsConstructibleSetSheaf B X (D.obj j) := by
    rintro (_ | _)
    · exact hR
    · exact hP
  let _ : EffectiveEpi q := (isRegularEpi_iff_effectiveEpi q).mp
    (IsRegularEpiCategory.regularEpiOfEpi q)
  have hq : IsColimit (Cofork.ofπ q pullback.condition) :=
    isColimitCoforkOfEffectiveEpi q (pullback.cone q q) (pullback.isLimit q q)
  let hc : IsColimit (Cocone.mk G (Cofork.ofπ q pullback.condition).ι) := hq
  exact isConstructibleSetSheaf_congr B X
    ((colimit.isColimit D).coconePointUniqueUpToIso hc) (isConstructibleSetSheaf_colimit B X D hD)

/-- Sub-closure descends along an epimorphic cover. If every subobject of `P` and of `P × P` is
constructible and `P` surjects onto `F`, then every subobject of `F` is constructible: pulling
the subobject back along the surjection gives a surjection onto it from a subobject of `P`, whose
kernel pair is a subobject of `P × P`. -/
private theorem isConstructibleSetSheaf_of_mono_of_epi_cover
    (B : BigEtaleSite.{u}) (X : B.Scheme)
    {P F G : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))}
    (p : P ⟶ F) [Epi p] (i : G ⟶ F) [Mono i]
    (hP : ∀ {H} (m : H ⟶ P), [Mono m] → IsConstructibleSetSheaf B X H)
    (hPP : ∀ {H} (m : H ⟶ P ⨯ P), [Mono m] → IsConstructibleSetSheaf B X H) :
    IsConstructibleSetSheaf B X G := by
  let H := pullback p i
  let m : H ⟶ P := pullback.fst p i
  let q : H ⟶ G := pullback.snd p i
  let J := SmallEtale.topology B X.obj X.property
  have hp : Presheaf.IsLocallySurjective J p.hom :=
    (Sheaf.isLocallySurjective_iff_epi p).2 inferInstance
  have hq : Presheaf.IsLocallySurjective J q.hom := by
    refine ⟨fun {U} s => ?_⟩
    apply J.superset_covering
      (S := Presheaf.imageSieve p.hom (i.hom.app (Opposite.op U) s))
      ?_ (hp.imageSieve_mem _)
    intro V f hf
    obtain ⟨t, ht⟩ := hf
    have heq : p.hom.app (Opposite.op V) t =
        i.hom.app (Opposite.op V) (G.obj.map f.op s) := by
      simpa only [i.hom.naturality_apply f.op s] using ht
    obtain ⟨k, -, hk⟩ := Sheaf.exists_pullback_section p i t (G.obj.map f.op s) heq
    exact ⟨k, hk⟩
  let r : pullback q q ⟶ P ⨯ P :=
    prod.lift (pullback.fst q q) (pullback.snd q q) ≫ prod.map m m
  have hr : Mono r := mono_comp' (mono_pullback_to_prod q q) (prod.map_mono m m)
  exact isConstructibleSetSheaf_of_epi_of_kernelPair B X q (hP m) (hPP r)

/-- The small étale topology of Stacks 021B is subcanonical: a representable presheaf on it is
the restriction of a representable presheaf on all schemes over the base, which is an fpqc sheaf,
and the étale topology is coarser than the fpqc topology. -/
public theorem smallEtaleTopology_subcanonical' (B : BigEtaleSite.{u}) (X : B.Scheme) :
    (SmallEtale.topology B X.obj X.property).Subcanonical := by
  let H := SmallEtale.inclusion B X.obj X.property ⋙ Over.post B.inclusion
  apply GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj
  intro U
  let e : H.op ⋙ yoneda.obj (H.obj U) ≅ yoneda.obj U :=
    NatIso.ofComponents
      (fun V => (Functor.FullyFaithful.ofFullyFaithful H).homEquiv.symm.toIso)
      (fun f => by
        ext g
        apply H.map_injective
        simp)
  apply (isSheaf_iff_isSheaf_of_type _ _).mp
  apply (Presheaf.isSheaf_of_iso_iff e).mp
  exact isSheaf_chosenSmallEtale_of_isSheaf_fpqc B X.obj X.property _
    ((isSheaf_iff_isSheaf_of_type _ _).mpr
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _))

/-- The fibre of a map to a representable presheaf over the tautological section: the presheaf on
the slice at `U` whose sections over `V ⟶ U` are the sections of `F` lying over it. -/
@[sga "3 I 1.4"]
private def representableFiber
    {C : Type w} [Category.{v} C] {U : C}
    {F : Cᵒᵖ ⥤ Type (max v t)} (i : F ⟶ uliftYoneda.{t}.obj U) :
    (Over U)ᵒᵖ ⥤ Type (max v t) where
  obj W := {s : F.obj (Opposite.op W.unop.left) //
    i.app (Opposite.op W.unop.left) s = ULift.up W.unop.hom}
  map {W W'} g := TypeCat.ofHom fun s => ⟨F.map g.unop.left.op s.1, by
    rw [NatTrans.naturality_apply, s.2]
    exact congrArg ULift.up (Over.w g.unop)⟩
  map_id _ := by ext s; simp
  map_comp f g := by
    ext s
    change F.map (f.unop.left.op ≫ g.unop.left.op) s.1 =
      F.map g.unop.left.op (F.map f.unop.left.op s.1)
    exact F.map_comp_apply _ _ _

/-- The fibre presheaf includes into the restriction of `F` to the slice. -/
private def representableFiberInclusion
    {C : Type w} [Category.{v} C] {U : C}
    {F : Cᵒᵖ ⥤ Type (max v t)} (i : F ⟶ uliftYoneda.{t}.obj U) :
    representableFiber i ⟶ (Over.forget U).op ⋙ F where
  app _ := TypeCat.ofHom Subtype.val
  naturality _ _ _ := rfl

/-- The fibre of a map of sheaves to a representable sheaf is a sheaf on the slice site. -/
private theorem isSheaf_representableFiber
    {C : Type w} [Category.{v} C] (J : GrothendieckTopology C) [J.Subcanonical]
    {U : C} {F : Sheaf J (Type (max v t))} (i : F.obj ⟶ uliftYoneda.{t}.obj U) :
    Presheaf.IsSheaf (J.over U) (representableFiber i) := by
  rw [isSheaf_iff_isSheaf_of_type]
  have hF := (isSheaf_iff_isSheaf_of_type _ _).1 (F.over U).property
  have hA := ((isSheaf_iff_isSheaf_of_type _ _).1
    ((J.uliftYoneda.{t}.obj U).over U).property).isSeparated
  intro W S hS x hx
  obtain ⟨s, hs, hsu⟩ := hF S hS (x.map (representableFiberInclusion i)) (hx.map _)
  have hm : i.app (Opposite.op W.left) s = ULift.up W.hom := by
    refine (hA S hS).ext (fun {Y} {f} hf => ?_)
    show (uliftYoneda.obj U).map f.left.op (i.app _ s) =
      ULift.up (f.left ≫ W.hom)
    calc
      _ = i.app _ (F.obj.map f.left.op s) :=
        (i.naturality_apply f.left.op s).symm
      _ = i.app _ (x f hf).1 := congrArg (i.app _) (hs f hf)
      _ = ULift.up Y.hom := (x f hf).2
      _ = _ := congrArg ULift.up (Over.w f).symm
  refine ⟨⟨s, hm⟩, fun _ f hf => Subtype.ext (hs f hf), fun y hy => Subtype.ext ?_⟩
  exact hsu y.1 (fun _ f hf => congrArg Subtype.val (hy f hf))

/-- The fibre of a map of sheaves to a representable sheaf, as a sheaf on the slice site. -/
private def representableFiberSheaf
    {C : Type w} [Category.{v} C] (J : GrothendieckTopology C) [J.Subcanonical]
    {U : C} {F : Sheaf J (Type (max v t))} (i : F ⟶ J.uliftYoneda.{t}.obj U) :
    Sheaf (J.over U) (Type (max v t)) :=
  ⟨representableFiber i.hom, isSheaf_representableFiber J i.hom⟩

/-- A monomorphism of sheaves of sets on a subcanonical site is injective on sections. -/
private theorem injective_app_of_mono_sheaf
    {C : Type w} [Category.{v} C] (J : GrothendieckTopology C) [J.Subcanonical]
    {F G : Sheaf J (Type (max v t))} (f : F ⟶ G) [Mono f] (T : Cᵒᵖ) :
    Function.Injective (f.hom.app T) := by
  intro a b h
  apply J.uliftYonedaEquiv.symm.injective
  apply (cancel_mono f).mp
  apply J.uliftYonedaEquiv.injective
  simpa only [GrothendieckTopology.uliftYonedaEquiv_comp, Equiv.apply_symm_apply] using h

/-- The fibre of a *monomorphism* into a representable sheaf is subterminal: a section lying over
a given arrow is unique. -/
private theorem isSubterminal_representableFiberSheaf
    {C : Type w} [Category.{v} C] (J : GrothendieckTopology C) [J.Subcanonical]
    {U : C} {F : Sheaf J (Type (max v t))} (i : F ⟶ J.uliftYoneda.{t}.obj U)
    [Mono i] : IsSubterminal (representableFiberSheaf J i) := by
  intro T a b
  ext W s
  exact Subtype.ext (injective_app_of_mono_sheaf J i (Opposite.op W.unop.left)
    (((a.hom.app W s).2).trans ((b.hom.app W s).2).symm))

/-- If a faithful functor sends `A` to a subobject of a subterminal object, `A` is subterminal. -/
private theorem isSubterminal_of_faithful_of_mono
    {C : Type*} [Category C] {D : Type*} [Category D] (G : C ⥤ D) [G.Faithful]
    {A : C} {B : D} (f : G.obj A ⟶ B) [Mono f] (hB : IsSubterminal B) : IsSubterminal A := by
  intro T a b
  exact G.map_injective ((cancel_mono f).mp (hB _ _))

/-- Restricting a representable presheaf along a fully faithful functor gives the presheaf
represented by the preimage object. -/
private def uliftYonedaWhiskerIso
    {C D : Type*} [Category.{v} C] [Category.{v} D]
    (H : C ⥤ D) [H.Full] [H.Faithful] (V : C) :
    H.op ⋙ uliftYoneda.{t}.obj (H.obj V) ≅ uliftYoneda.{t}.obj V := by
  refine NatIso.ofComponents (fun T =>
    ((Equiv.ulift).trans ((Functor.FullyFaithful.ofFullyFaithful H).homEquiv.symm.trans
      Equiv.ulift.symm)).toIso) ?_
  intro T T' f
  ext x
  apply ULift.ext
  change H.preimage (H.map f.unop ≫ x.down) = f.unop ≫ H.preimage x.down
  rw [H.preimage_comp, H.preimage_map]

/-- A subobject of a representable sheaf whose fibre is represented by an object `V` of the slice
is itself represented, by the source of `V`. -/
private def representableIsoOfFiber
    {C : Type w} [Category.{v} C] (J : GrothendieckTopology C) [J.Subcanonical]
    {U : C} {F : Sheaf J (Type (max v t))} (i : F ⟶ J.uliftYoneda.{t}.obj U)
    [Mono i] (V : Over U)
    (e : representableFiberSheaf J i ≅ (J.over U).uliftYoneda.{t}.obj V) :
    J.uliftYoneda.{t}.obj V.left ≅ F := by
  have hV : IsSubterminal V :=
    isSubterminal_of_faithful_of_mono (J.over U).uliftYoneda.{t} e.inv
      (isSubterminal_representableFiberSheaf J i)
  have : Mono V.hom := ⟨fun a b h => congrArg Over.Hom.left
    (hV (Over.homMk a (by rfl) : Over.mk (a ≫ V.hom) ⟶ V) (Over.homMk b h.symm))⟩
  let s := e.inv.hom.app (Opposite.op V) (ULift.up (𝟙 V))
  let k : J.uliftYoneda.{t}.obj V.left ⟶ F := J.uliftYonedaEquiv.symm s.1
  have hk : k ≫ i = J.uliftYoneda.map V.hom := by
    ext T a
    change ULift.{t} (T.unop ⟶ V.left) at a
    change i.hom.app T (F.obj.map a.down.op s.1) = ULift.up (a.down ≫ V.hom)
    rw [i.hom.naturality_apply]
    exact congrArg (fun z : ULift.{t} (V.left ⟶ U) =>
      ULift.up (a.down ≫ z.down)) s.2
  have : Mono k := mono_of_mono_fac hk
  have (T : Cᵒᵖ) : IsIso (k.hom.app T) := by
    apply (CategoryTheory.isIso_iff_bijective _).2
    refine ⟨injective_app_of_mono_sheaf J k T, ?_⟩
    intro a
    let f := (i.hom.app T a).down
    let b : (representableFiberSheaf J i).obj.obj (Opposite.op (Over.mk f)) := ⟨a, rfl⟩
    let g := (e.hom.hom.app (Opposite.op (Over.mk f)) b).down
    refine ⟨ULift.up g.left, ?_⟩
    apply (injective_app_of_mono_sheaf J i T)
    have hk' := congrArg (fun z => z.hom.app T (ULift.up g.left)) hk
    exact hk'.trans (congrArg ULift.up (Over.w g))
  have : IsIso k.hom := NatIso.isIso_of_isIso_app k.hom
  exact (fullyFaithfulSheafToPresheaf J _).preimageIso (asIso k.hom)

/-- **A subterminal sheaf of sets on the small étale site of a Noetherian scheme is represented by
a quasi-compact object.** Stacks 04HV represents it by an open subscheme, and an open subscheme of
a Noetherian scheme is quasi-compact and quasi-separated. -/
private theorem exists_representable_of_subterminal
    (B : BigEtaleSite.{u}) (X : B.Scheme) [IsNoetherian X.obj]
    [hJ : (SmallEtale.topology B X.obj X.property).Subcanonical]
    {F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))}
    (hF : IsSubterminal F) :
    ∃ V : SmallEtale B X.obj X.property,
      CompactSpace ((SmallEtale.toScheme B X.obj X.property).obj V) ∧
      QuasiSeparatedSpace ((SmallEtale.toScheme B X.obj X.property).obj V) ∧
      Nonempty (F ≅
        (SmallEtale.topology B X.obj X.property).uliftYoneda.{u + 1}.obj V) := by
  obtain ⟨W, ⟨e⟩, -⟩ :=
    existsUnique_open_of_isSubterminal.{u, 0} B X.obj X.property F hF
  let Z : B.Scheme := ⟨W.toScheme,
    lt_of_le_of_lt (Scheme.size_coe_opens_le X.obj W) X.property⟩
  let f : Z ⟶ X := B.inclusion.preimage
    (show B.inclusion.obj Z ⟶ B.inclusion.obj X from W.ι)
  have hf : B.inclusion.map f = W.ι := by
    show B.inclusion.map (B.inclusion.preimage
      (show B.inclusion.obj Z ⟶ B.inclusion.obj X from W.ι)) = W.ι
    rw [Functor.map_preimage]
  let V : SmallEtale B X.obj X.property := ⟨Over.mk f, by
    show Etale (B.inclusion.map f)
    rw [hf]
    infer_instance⟩
  let H : SmallEtale B X.obj X.property ⥤
      Over (B.inclusion.obj (B.obj X.obj X.property)) :=
    SmallEtale.inclusion B X.obj X.property ⋙
      Over.post (X := B.obj X.obj X.property) B.inclusion
  let eV : H.obj V ≅ Over.mk W.ι := by
    refine Over.isoMk (Iso.refl _) ?_
    show W.ι = B.inclusion.map f
    exact hf.symm
  let isoRep : (H.op ⋙ uliftYoneda.{u + 1}.obj (Over.mk W.ι)) ≅ uliftYoneda.{u + 1}.obj V :=
    Functor.isoWhiskerLeft H.op (uliftYoneda.{u + 1}.mapIso eV.symm) ≪≫ uliftYonedaWhiskerIso H V
  have : CompactSpace ((SmallEtale.toScheme B X.obj X.property).obj V) := by
    show CompactSpace W.toScheme
    exact isCompact_iff_compactSpace.mp
      (TopologicalSpace.NoetherianSpace.isCompact (W : Set X.obj))
  have : QuasiSeparatedSpace ((SmallEtale.toScheme B X.obj X.property).obj V) := by
    show QuasiSeparatedSpace W.toScheme
    infer_instance
  exact ⟨V, inferInstance, inferInstance, ⟨e ≪≫ (presheafToSheaf _ _).mapIso isoRep ≪≫
    (sheafificationIso ((SmallEtale.topology B X.obj X.property).uliftYoneda.obj V)).symm⟩⟩

/-- **A subobject of a quasi-compact representable sheaf of sets on a Noetherian scheme is
constructible.** Its fibre over the tautological section is a subterminal sheaf on the small étale
site of the representing object, hence represented by an open subscheme there; that open is
quasi-compact and quasi-separated, so the subobject is a quasi-compact representable sheaf and
`hrep` applies. -/
private theorem isConstructibleSetSheaf_of_mono_representable
    (B : BigEtaleSite.{u}) (X : B.Scheme) [IsNoetherian X.obj]
    (hrep : RepresentableIsConstructibleSetSheaf B X)
    (U : SmallEtale B X.obj X.property)
    [CompactSpace ((SmallEtale.toScheme B X.obj X.property).obj U)]
    {F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))}
    (i : F ⟶ (Sheaf.sheafifiedYoneda
      (SmallEtale.topology B X.obj X.property)).obj U) [Mono i] :
    IsConstructibleSetSheaf B X F := by
  let J := SmallEtale.topology B X.obj X.property
  let JU := SmallEtale.topology B U.obj.left.obj U.obj.left.property
  let : J.Subcanonical := smallEtaleTopology_subcanonical' B X
  let : JU.Subcanonical := smallEtaleTopology_subcanonical' B U.obj.left
  let : IsLocallyNoetherian (B.inclusion.obj (B.obj X.obj X.property)) :=
    inferInstanceAs (IsLocallyNoetherian X.obj)
  let : IsLocallyNoetherian U.obj.left.obj :=
    LocallyOfFiniteType.isLocallyNoetherian (B.inclusion.map U.obj.hom)
  let : CompactSpace U.obj.left.obj :=
    inferInstanceAs (CompactSpace ((SmallEtale.toScheme B X.obj X.property).obj U))
  let : IsNoetherian U.obj.left.obj := ⟨⟩
  let e := sheafificationIso (J.uliftYoneda.{u + 1}.obj U)
  let j : F ⟶ J.uliftYoneda.{u + 1}.obj U := i ≫ e.inv
  have he : Mono e.inv := ⟨fun a b h => by
    calc a = a ≫ e.inv ≫ e.hom := by simp
      _ = b ≫ e.inv ≫ e.hom := congrArg (· ≫ e.hom) h
      _ = b := by simp⟩
  have : Mono j := mono_comp' (inferInstance : Mono i) he
  let E := SmallEtale.localizationEquivalence B X.obj X.property U
  have htop : E.functor.inducedTopology (J.over U) = JU :=
    SmallEtale.localizationEquivalence_topology B X.obj X.property U
  let : E.functor.IsDenseSubsite JU (J.over U) := by
    rw [← htop]
    infer_instance
  let : E.symm.inverse.IsDenseSubsite JU (J.over U) :=
    inferInstanceAs (E.functor.IsDenseSubsite JU (J.over U))
  let ES := E.symm.sheafCongr (J.over U) JU (Type (u + 1))
  obtain ⟨V, hVc, hVq, ⟨eV⟩⟩ := exists_representable_of_subterminal B U.obj.left
    (isSubterminal_of_faithful_of_mono ES.inverse (ES.unitIso.inv.app _)
      (isSubterminal_representableFiberSheaf J j))
  let W := E.functor.obj V
  let eR : ES.functor.obj ((J.over U).uliftYoneda.{u + 1}.obj W) ≅
      JU.uliftYoneda.{u + 1}.obj V :=
    ObjectProperty.isoMk _ (uliftYonedaWhiskerIso E.functor V)
  let eA : representableFiberSheaf J j ≅ (J.over U).uliftYoneda.{u + 1}.obj W :=
    ES.functor.preimageIso (eV ≪≫ eR.symm)
  let eF := representableIsoOfFiber J j W eA
  have hW : W = SmallEtale.localizationObj B X.obj X.property U V :=
    SmallEtale.localizationEquivalence_obj B X.obj X.property U V
  have hWc : CompactSpace ((SmallEtale.toScheme B X.obj X.property).obj W.left) := by
    rw [hW]
    exact hVc
  have hWq : QuasiSeparatedSpace ((SmallEtale.toScheme B X.obj X.property).obj W.left) := by
    rw [hW]
    exact hVq
  exact isConstructibleSetSheaf_congr B X
    ((sheafificationIso (J.uliftYoneda.{u + 1}.obj W.left)).symm ≪≫ eF)
    (hrep W.left hWc hWq)

/-- A product of two quasi-compact objects of the small étale site of a quasi-separated scheme is
quasi-compact: the product is the fibre product over the base, and a fibre product of
quasi-compact schemes over a quasi-separated base is quasi-compact. -/
private theorem compactSpace_smallEtale_prod
    (B : BigEtaleSite.{u}) (X : B.Scheme) [QuasiSeparatedSpace X.obj]
    (U V : SmallEtale B X.obj X.property)
    [CompactSpace ((SmallEtale.toScheme B X.obj X.property).obj U)]
    [CompactSpace ((SmallEtale.toScheme B X.obj X.property).obj V)] :
    CompactSpace ((SmallEtale.toScheme B X.obj X.property).obj (U ⨯ V)) := by
  let H := SmallEtale.toScheme B X.obj X.property
  let T := SmallEtale.finalIsTerminal B X.obj X.property
  have hp := (IsPullback.of_isLimit_binaryFan_of_isTerminal (prodIsProd U V) T).map H
  let : CompactSpace (H.obj U) := inferInstanceAs
    (CompactSpace ((SmallEtale.toScheme B X.obj X.property).obj U))
  let : CompactSpace (H.obj V) := inferInstanceAs
    (CompactSpace ((SmallEtale.toScheme B X.obj X.property).obj V))
  let : QuasiSeparatedSpace (H.obj (SmallEtale.final B X.obj X.property)) :=
    inferInstanceAs (QuasiSeparatedSpace X.obj)
  have : QuasiCompact (H.map (T.from U)) := quasiCompact_of_compactSpace _
  have : CompactSpace ↑(pullback (H.map (T.from U)) (H.map (T.from V))) := inferInstance
  let e : H.obj (U ⨯ V) ≅ pullback (H.map (T.from U)) (H.map (T.from V)) := hp.isoPullback
  exact (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso e)).symm.compactSpace

/-- **Stacks 09BH, part (1), subsheaves.** A subsheaf of a constructible sheaf of sets on the
small étale site of a Noetherian scheme is constructible.

`hrep` is Stacks 03S8 and `hcover` is the surjection half of Stacks 09Y9; neither mentions
subobjects. Given a surjection onto `F` from a finite coproduct of quasi-compact representables,
sub-closure for the coproduct and for its square descends to `F`, and sub-closure for a
quasi-compact representable is `isConstructibleSetSheaf_of_mono_representable`. -/
@[stacks 09BH "part (1), subsheaf, with Stacks 03S8 as hrep and the surjection half of Stacks \
09Y9 as hcover"]
public theorem isConstructibleSetSheaf_of_mono (B : BigEtaleSite.{u})
    (X : B.Scheme) [IsNoetherian X.obj]
    (hrep : RepresentableIsConstructibleSetSheaf B X)
    (hcover : HasFiniteRepresentableCover B X)
    {F G : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))}
    (i : G ⟶ F) [Mono i] (hF : IsConstructibleSetSheaf B X F) :
    IsConstructibleSetSheaf B X G := by
  obtain ⟨n, U, hU, p, hp⟩ := hcover F hF
  let := hp
  let A := fun j => (Sheaf.sheafifiedYoneda
    (SmallEtale.topology B X.obj X.property)).obj (U j)
  have hA : ∀ j, ∀ {H} (m : H ⟶ A j), [Mono m] → IsConstructibleSetSheaf B X H := by
    intro j H m _
    let := (hU j).1
    exact isConstructibleSetSheaf_of_mono_representable B X hrep (U j) m
  refine isConstructibleSetSheaf_of_mono_of_epi_cover B X p i
    (fun m _ => isConstructibleSetSheaf_of_mono_coproduct B X A hA m) fun m _ => ?_
  refine isConstructibleSetSheaf_of_mono_coproduct B X (fun q : Fin n × Fin n => A q.1 ⨯ A q.2)
    (fun q K k _ => ?_) (m ≫ (finiteCoproductProductIso A A).hom)
  let := (hU q.1).1
  let := (hU q.2).1
  let := compactSpace_smallEtale_prod B X (U q.1) (U q.2)
  exact isConstructibleSetSheaf_of_mono_representable B X hrep (U q.1 ⨯ U q.2)
    (k ≫ (sheafifiedYonedaProductIso B X (U q.1) (U q.2)).hom)

/-- **Stacks 09BH, part (1), quotient sheaves.** A quotient sheaf of a constructible sheaf of sets
on the small étale site of a Noetherian scheme is constructible.

This is the source's argument: the kernel pair `ℱ ×_𝒬 ℱ` is a subsheaf of `ℱ × ℱ`, hence
constructible by the subsheaf case and Stacks 03RZ (1), and `𝒬` is the coequalizer of that kernel
pair, hence constructible by Stacks 03RZ (1) again. -/
@[stacks 09BH "part (1), quotient sheaf, with Stacks 03S8 as hrep and the surjection half of \
Stacks 09Y9 as hcover"]
public theorem isConstructibleSetSheaf_of_epi (B : BigEtaleSite.{u})
    (X : B.Scheme) [IsNoetherian X.obj]
    (hrep : RepresentableIsConstructibleSetSheaf B X)
    (hcover : HasFiniteRepresentableCover B X)
    {F Q : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))}
    (p : F ⟶ Q) [Epi p] (hF : IsConstructibleSetSheaf B X F) :
    IsConstructibleSetSheaf B X Q := by
  let ι : pullback p p ⟶ F ⨯ F := prod.lift (pullback.fst p p) (pullback.snd p p)
  have hι : Mono ι := mono_pullback_to_prod p p
  exact isConstructibleSetSheaf_of_epi_of_kernelPair B X p hF
    (isConstructibleSetSheaf_of_mono B X hrep hcover ι
      (isConstructibleSetSheaf_prod B X hF hF))

end AlgebraicGeometry

end
