module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ReasonableFilteredApproximation.QuotientDiagram
import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismProperties
import StacksFrontier.AlgebraicGeometry.Spaces.RelativeNormalization
import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks 03K0: existence of a corrected directed approximation

The quasi-separatedness of the test schemes used in clause (1), the scheme case (clause (3)):
local isomorphisms and representability of the stages, and the main theorem
`AlgebraicGeometry.Space.exists_correctedDirectedApproximation`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] ReasonableApproximation.schemeCutoff_isClosedUnderIsomorphisms
  ReasonableApproximation.schemeCutoff_isClosedUnderLimitsOfShape_walkingCospan
  ReasonableApproximation.schemeCutoff_hasTerminal
  ReasonableApproximation.schemeCutoff_hasPullbacks

namespace ReasonableApproximation

universe u₁ u₂ v₁ v₂

/-- For `v : W ⟶ T` with `W` quasi-compact and `T` quasi-separated, the fibre product `W ×_T W` is
quasi-compact. **This is the only place quasi-separatedness of the test scheme is used**, and
the reason clause (1) must be restricted to quasi-separated test schemes. -/
private theorem compactSpace_pullback_of_compact_of_quasiSeparated
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {W T : AlgebraicGeometry.BigFppfOver B S hS} (v : W ⟶ T)
    [CompactSpace ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj W)]
    [QuasiSeparatedSpace ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T)] :
    CompactSpace ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (pullback v v)) := by
  let G := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let e := ((IsPullback.of_hasPullback v v).map G).isoPullback
  exact e.inv.homeomorph.compactSpace

/-- A morphism `f : T ⟶ R` of the site with `T` quasi-compact factors through `openObject R A` for
some open `A` satisfying `P`, when every quasi-compact open of `R` is contained in one
satisfying `P`. -/
private theorem exists_factorization_through_site_open_envelope
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T R : AlgebraicGeometry.BigFppfOver B S hS}
    [CompactSpace ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T)]
    (f : T ⟶ R)
    (P : ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj R).Opens → Prop)
    (hP : ∀ A : ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj R).Opens,
      IsCompact (A : Set ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj R)) →
      ∃ A', P A' ∧ A ≤ A') :
    ∃ (A : ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj R).Opens), P A ∧
      ∃ g : T ⟶ openObject B S hS R A, g ≫ openObjectι B S hS R A = f := by
  obtain ⟨A, hA, g, hg⟩ := exists_factorization_through_open_envelope
    ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map f) P hP
  refine ⟨A, hA, Over.homMk (ObjectProperty.homMk g) ?_, ?_⟩
  · apply ObjectProperty.hom_ext
    show g ≫ (A.ι ≫ R.hom.hom) = T.hom.hom
    rw [← Category.assoc, hg]
    exact congrArg (fun f => f.hom) f.w
  · apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact hg

/-- For a surjective étale morphism `v : W ⟶ T` of the site, the sheaf represented by `T` is the
coequalizer of the kernel pair of the sheaf morphism represented by `v`. -/
private noncomputable def sheafIsColimitOfSurjectiveEtale
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [HasSheafify (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type u)]
    {W T : AlgebraicGeometry.BigFppfOver B S hS} (v : W ⟶ T)
    [Surjective ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map v)]
    [Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map v)] :
    IsColimit (Cofork.ofπ ((sheafOfSchemeFunctor B S hS).map v)
      (show (sheafOfSchemeFunctor B S hS).map (pullback.fst v v) ≫
        (sheafOfSchemeFunctor B S hS).map v =
        (sheafOfSchemeFunctor B S hS).map (pullback.snd v v) ≫
        (sheafOfSchemeFunctor B S hS).map v from by
          rw [← Functor.map_comp, ← Functor.map_comp, pullback.condition])) :=
  sheafKernelPairIsColimit _ _ _ _ ((IsPullback.of_hasPullback v v).map yoneda)
    (atlas_isLocallySurjective B S hS (Y := sheafOfScheme B S hS T) (yoneda.map v)
      (presheaf_yoneda_map_of_inverseImage B S hS (P := @Surjective.{u}) inferInstance v
        inferInstance)
      (presheaf_yoneda_map_of_inverseImage B S hS (P := @Etale.{u}) inferInstance v
        inferInstance))

/-- An étale morphism `g` such that `g ≫ f` is an open immersion is itself an open immersion: it is
monic and flat. -/
private theorem isOpenImmersion_of_etale_of_comp
    {U V T : Scheme.{u}} (g : U ⟶ V) (f : V ⟶ T) [Etale g]
    [_root_.AlgebraicGeometry.IsOpenImmersion (g ≫ f)] :
    _root_.AlgebraicGeometry.IsOpenImmersion g :=
  have : Mono g := mono_of_mono g f
  IsOpenImmersion.of_flat_of_mono g

/-- If `q` is étale and `q ≫ f` is a local isomorphism, then `q` is a local isomorphism: on a
suitable open of the source, `q` is monic and flat, hence an open immersion. -/
private theorem isLocalIso_of_comp_of_etale
    {U V T : Scheme.{u}} (q : U ⟶ V) (f : V ⟶ T)
    [Etale q] [IsLocalIso (q ≫ f)] : IsLocalIso q := by
  constructor
  intro x
  obtain ⟨A, hx, hA⟩ := IsLocalIso.exists_isOpenImmersion (f := q ≫ f) x
  let : _root_.AlgebraicGeometry.IsOpenImmersion ((A.ι ≫ q) ≫ f) := by
    simpa only [Category.assoc] using hA
  exact ⟨A, hx, isOpenImmersion_of_etale_of_comp (A.ι ≫ q) f⟩

/-- If `q` is surjective étale and `q ≫ f` is a local isomorphism, then `f` is a local isomorphism:
the opens on which `q ≫ f` is an open immersion cover the source, and their images under `q`
cover the target. -/
private theorem isLocalIso_of_comp_surjective_etale
    {U V T : Scheme.{u}} (q : U ⟶ V) (f : V ⟶ T)
    [Surjective q] [Etale q] [IsLocalIso (q ≫ f)] : IsLocalIso f := by
  classical
  choose A hx hA using IsLocalIso.exists_isOpenImmersion (f := q ≫ f)
  have hq (x : U) : _root_.AlgebraicGeometry.IsOpenImmersion ((A x).ι ≫ q) := by
    let : _root_.AlgebraicGeometry.IsOpenImmersion (((A x).ι ≫ q) ≫ f) := by
      simpa only [Category.assoc] using hA x
    exact isOpenImmersion_of_etale_of_comp ((A x).ι ≫ q) f
  let V' : V.OpenCover := ⟨⟨U, fun x => (A x).toScheme, fun x => (A x).ι ≫ q⟩,
    (Scheme.ofArrows_mem_precoverage_iff _).mpr ⟨fun y => by
      obtain ⟨x, rfl⟩ := Surjective.surj (f := q) y
      exact ⟨x, ⟨x, hx x⟩, rfl⟩, hq⟩⟩
  apply IsZariskiLocalAtSource.of_openCover (P := @IsLocalIso) V'
  intro x
  let : _root_.AlgebraicGeometry.IsOpenImmersion ((V'.f x) ≫ f) := by
    show _root_.AlgebraicGeometry.IsOpenImmersion (((A x).ι ≫ q) ≫ f)
    simpa only [Category.assoc] using hA x
  exact ⟨fun y => ⟨⊤, trivial, inferInstance⟩⟩

/-- A monomorphism of presheaves whose relative form is étale is an open immersion: each
representing base change is étale and monic, hence an open immersion of schemes. -/
private theorem isOpenImmersion_of_relative_etale_mono
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (q : F ⟶ Z) [Mono q]
    (hq : (MorphismProperty.inverseImage (@Etale.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf q) :
    IsOpenImmersion B S hS q := by
  refine ⟨hq.1, ?_⟩
  intro T W ξ a v hp
  let G := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let : Etale (G.map v) := hq.2 ξ a v hp
  let : Mono (yoneda.map v) := hp.mono_snd_of_mono
  let : Mono v := Functor.mono_of_mono_map yoneda inferInstance
  let : PreservesLimitsOfShape WalkingCospan G := inferInstance
  let : Mono (G.map v) := inferInstance
  exact IsOpenImmersion.of_flat_of_mono (G.map v)

/-- The morphism out of the coproduct of the representables of a covering family,
`Sigma.desc (fun i ↦ yoneda.map (v i))`, is locally surjective. -/
private theorem presheaf_isLocallySurjective_sigma_of_cover
    {C : Type u₁} [Category.{u₂} C] (J : GrothendieckTopology C)
    {T : C} {I : Type u₂} (W : I → C) (v : ∀ i, W i ⟶ T)
    (hcover : Sieve.ofArrows W v ∈ J T) :
    Presheaf.IsLocallySurjective J (Limits.Sigma.desc (fun i => yoneda.map (v i))) := by
  constructor
  intro V t
  apply J.superset_covering _ (J.pullback_stable t hcover)
  intro A g hg
  obtain ⟨i, k, hk⟩ := (Sieve.mem_ofArrows_iff W v (g ≫ t)).mp hg
  refine ⟨(Limits.Sigma.ι (fun i => yoneda.obj (W i)) i).app (op A) k, ?_⟩
  show ((Limits.Sigma.ι (fun i => yoneda.obj (W i)) i ≫
    Limits.Sigma.desc (fun i => yoneda.map (v i))).app (op A)) k = g ≫ t
  rw [Limits.Sigma.ι_desc]
  exact hk.symm

/-- An algebraic space covered by a jointly locally surjective family of open immersions from
representables is representable, the family being a Zariski cover by subfunctors. -/
private theorem isRepresentable_of_open_atlas
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZ : AlgebraicGeometry.IsAlgebraicSpace B S hS Z)
    {I : Type u} (W : I → AlgebraicGeometry.BigFppfOver B S hS)
    (a : ∀ i, yoneda.obj (W i) ⟶ Z) (ha : ∀ i, Mono (a i))
    (hoa : ∀ i, IsOpenImmersion B S hS (a i))
    (hcov : Presheaf.IsLocallySurjective (AlgebraicGeometry.BigFppfOver.topology B S hS)
      (Sigma.desc a)) : Z.IsRepresentable := by
  let := ha
  let V (i : I) := Subfunctor.range (a i)
  apply isRepresentable_of_isZariskiCover B S hS Z hZ I V
  · refine ⟨fun i => ⟨?_, ?_⟩, ?_⟩
    · exact isAlgebraicSpace_of_iso B S hS (asIso (Subfunctor.toRange (a i)))
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (W i))
    · apply (MorphismProperty.cancel_left_of_respectsIso _
        (Subfunctor.toRange (a i)) (V i).ι).mp
      simpa only [V, Subfunctor.toRange_ι] using hoa i
    · let b := Sigma.desc (fun i => Subfunctor.toRange (a i) ≫ Sigma.ι (fun i => (V i).toFunctor) i)
      have hb : b ≫ Sigma.desc (fun i => (V i).ι) = Sigma.desc a := by
        apply Sigma.hom_ext
        intro i
        simp [b, V]
      have : Presheaf.IsLocallySurjective (AlgebraicGeometry.BigFppfOver.topology B S hS)
          (b ≫ Sigma.desc (fun i => (V i).ι)) := hb.symm ▸ hcov
      exact Presheaf.isLocallySurjective_of_isLocallySurjective _ b _
  · intro i
    exact Functor.IsRepresentable.mk' (asIso (Subfunctor.toRange (a i)))

/-- If an algebraic space `Z` has an étale locally surjective atlas `q : yoneda.obj U ⟶ Z` and a
morphism `f : Z ⟶ yoneda.obj T` with `q ≫ f = yoneda.map p` for a local isomorphism `p`, then
`Z` is representable: the opens of `U` on which `p` is an open immersion give an open atlas of
`Z`. -/
private theorem isRepresentable_of_localIso_composite
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U T : AlgebraicGeometry.BigFppfOver B S hS}
    {Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZ : AlgebraicGeometry.IsAlgebraicSpace B S hS Z)
    (q : yoneda.obj U ⟶ Z) (f : Z ⟶ yoneda.obj T) (p : U ⟶ T)
    (hcomp : q ≫ f = yoneda.map p)
    (hq : (MorphismProperty.inverseImage (@Etale.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf q)
    (hqs : Presheaf.IsLocallySurjective (AlgebraicGeometry.BigFppfOver.topology B S hS) q)
    (hp : IsLocalIso ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map p)) :
    Z.IsRepresentable := by
  classical
  let G := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let := hp
  choose A hx hA using IsLocalIso.exists_isOpenImmersion (f := G.map p)
  let W (x : G.obj U) := openObject B S hS U (A x)
  let v (x : G.obj U) : W x ⟶ U := openObjectι B S hS U (A x)
  let a (x : G.obj U) := yoneda.map (v x) ≫ q
  have ha (x : G.obj U) : Mono (a x) := by
    let : _root_.AlgebraicGeometry.IsOpenImmersion (G.map (v x ≫ p)) := hA x
    let : Mono (G.map (v x ≫ p)) := inferInstance
    let : Mono (v x ≫ p) := Functor.mono_of_mono_map G inferInstance
    have he : a x ≫ f = yoneda.map (v x ≫ p) := by
      dsimp only [a]
      rw [Category.assoc, hcomp, yoneda.map_comp]
    let : Mono (a x ≫ f) := he.symm ▸ inferInstanceAs (Mono (yoneda.map (v x ≫ p)))
    exact mono_of_mono (a x) f
  have hoa (x : G.obj U) : IsOpenImmersion B S hS (a x) := by
    let := ha x
    apply isOpenImmersion_of_relative_etale_mono B S hS
    let P := MorphismProperty.inverseImage (@Etale.{u}) G
    let : MorphismProperty.IsStableUnderComposition (@Etale.{u}) :=
      (inferInstance : MorphismProperty.IsMultiplicative (@Etale.{u})).toIsStableUnderComposition
    let : P.IsStableUnderComposition := MorphismProperty.IsStableUnderComposition.inverseImage G
    let : P.presheaf.IsStableUnderComposition :=
      MorphismProperty.relative_isStableUnderComposition P
    exact P.presheaf.comp_mem _ _
      (presheaf_yoneda_map_of_inverseImage B S hS (P := @Etale.{u}) inferInstance (v x)
        (inferInstanceAs (Etale (A x).ι))) hq
  apply isRepresentable_of_open_atlas B S hS hZ W a ha hoa
  have hcover : Sieve.ofArrows W v ∈ AlgebraicGeometry.BigFppfOver.topology B S hS U := by
    apply (AlgebraicGeometry.BigFppfOver.topology B S hS).superset_covering _
      (fppf_cover_sieve_mem B S hS (fun x : ULift.{u + 1} (G.obj U) => W x.down)
        (fun x => v x.down) (fun x => ⟨⟨x⟩, ⟨x, hx x⟩, rfl⟩) (fun x =>
          ⟨inferInstanceAs (Flat (A x.down).ι),
            inferInstanceAs (LocallyOfFinitePresentation (A x.down).ι)⟩))
    intro V g hg
    obtain ⟨x, k, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hg
    exact (Sieve.mem_ofArrows_iff _ _ _).mpr ⟨x.down, k, rfl⟩
  let : Presheaf.IsLocallySurjective (AlgebraicGeometry.BigFppfOver.topology B S hS)
      (Sigma.desc (fun x => yoneda.map (v x))) :=
    presheaf_isLocallySurjective_sigma_of_cover _ W v hcover
  let := hqs
  have he : Sigma.desc a = Sigma.desc (fun x => yoneda.map (v x)) ≫ q := by
    apply Sigma.hom_ext
    intro x
    simp [a]
  rw [he]
  infer_instance

/-- Conversely to `AlgebraicGeometry.Space.presheaf_yoneda_map_of_inverseImage`, the relative
form of a base-change-stable property for `p : yoneda.obj U ⟶ X` gives that property for the
scheme morphism `U ⟶ T` representing `p` along an isomorphism `yoneda.obj T ≅ X`. -/
private theorem property_of_yoneda_preimage_comp_iso
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    {U T : AlgebraicGeometry.BigFppfOver B S hS}
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (e : yoneda.obj T ≅ X) (p : yoneda.obj U ⟶ X)
    (hp : (P.inverseImage (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf p) :
    P ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (yoneda.preimage (p ≫ e.inv))) := by
  let G := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let : (P.inverseImage G).IsStableUnderBaseChange :=
    MorphismProperty.inverseImage_isStableUnderBaseChange G P
  refine (MorphismProperty.relative_map_iff (F := yoneda) (P := P.inverseImage G)).mp ?_
  rw [yoneda.map_preimage]
  exact MorphismProperty.RespectsIso.postcomp _ e.inv _ hp

/-- The relative form of a base-change-stable property for `yoneda.map f` transfers along an
isomorphism `yoneda.obj T ≅ X`. -/
private theorem presheaf_yoneda_map_comp_iso
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    {U T : AlgebraicGeometry.BigFppfOver B S hS}
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : U ⟶ T) (hf : P ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map f))
    (e : yoneda.obj T ≅ X) :
    (P.inverseImage (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf
      (yoneda.map f ≫ e.hom) :=
  MorphismProperty.RespectsIso.postcomp _ e.hom _
    (presheaf_yoneda_map_of_inverseImage B S hS inferInstance f hf)

/-- **Clause (3).** Let `X` be representable, `p : yoneda.obj U ⟶ X` a local-isomorphism atlas
factoring as `q ≫ f` through an algebraic space `Z` with `q` surjective étale. Then `Z` is
representable, and both `f` and `q` are local isomorphisms. -/
private theorem isRepresentable_and_localIso_of_localIso_atlas
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U : AlgebraicGeometry.BigFppfOver B S hS}
    {X Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZ : AlgebraicGeometry.IsAlgebraicSpace B S hS Z)
    (p : yoneda.obj U ⟶ X) (q : yoneda.obj U ⟶ Z) (f : Z ⟶ X)
    (hcomp : q ≫ f = p)
    (hp : (MorphismProperty.inverseImage (@IsLocalIso.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf p)
    (hq : (MorphismProperty.inverseImage (@Etale.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf q)
    (hqs : (MorphismProperty.inverseImage (@Surjective.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf q)
    (hX : X.IsRepresentable) : Z.IsRepresentable ∧
      (MorphismProperty.inverseImage (@IsLocalIso.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf f ∧
      (MorphismProperty.inverseImage (@IsLocalIso.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf q := by
  classical
  let := hX
  let G := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let T := X.reprX
  let eT : yoneda.obj T ≅ X := X.reprW
  let p₀ : U ⟶ T := yoneda.preimage (p ≫ eT.inv)
  have hp₀ : IsLocalIso (G.map p₀) := property_of_yoneda_preimage_comp_iso B S hS _ eT p hp
  have hcomp₀ : q ≫ (f ≫ eT.inv) = yoneda.map p₀ := by
    simp only [p₀, yoneda.map_preimage, ← Category.assoc, hcomp]
  have hzrep : Z.IsRepresentable :=
    isRepresentable_of_localIso_composite B S hS hZ q (f ≫ eT.inv) p₀ hcomp₀ hq
      (atlas_isLocallySurjective B S hS (Y := ⟨Z, hZ.isSheaf⟩) q hqs hq) hp₀
  refine ⟨hzrep, ?_⟩
  let := hzrep
  let V := Z.reprX
  let eV : yoneda.obj V ≅ Z := Z.reprW
  let q₀ : U ⟶ V := yoneda.preimage (q ≫ eV.inv)
  let f₀ : V ⟶ T := yoneda.preimage (eV.hom ≫ f ≫ eT.inv)
  have hf₀ : q₀ ≫ f₀ = p₀ := by
    apply yoneda.map_injective
    simp only [q₀, f₀, p₀, Functor.map_comp, yoneda.map_preimage,
      Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc, hcomp]
  let : Etale (G.map q₀) := property_of_yoneda_preimage_comp_iso B S hS _ eV q hq
  let : Surjective (G.map q₀) := property_of_yoneda_preimage_comp_iso B S hS _ eV q hqs
  let : IsLocalIso (G.map q₀ ≫ G.map f₀) := by
    rwa [← G.map_comp, hf₀]
  have hfl : IsLocalIso (G.map f₀) := isLocalIso_of_comp_surjective_etale (G.map q₀) (G.map f₀)
  refine ⟨?_, ?_⟩
  · have h := MorphismProperty.RespectsIso.precomp
      (MorphismProperty.inverseImage (@IsLocalIso.{u}) G).presheaf eV.inv _
      (presheaf_yoneda_map_comp_iso B S hS (@IsLocalIso.{u}) f₀ hfl eT)
    simpa only [f₀, yoneda.map_preimage, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
      Category.comp_id] using h
  · have h := presheaf_yoneda_map_comp_iso B S hS (@IsLocalIso.{u}) q₀
      (isLocalIso_of_comp_of_etale (G.map q₀) (G.map f₀)) eV
    simpa only [q₀, yoneda.map_preimage, Category.assoc, Iso.inv_hom_id, Category.comp_id] using h

/-- A quasi-compact object of the site is covered by an affine one through a surjective local
isomorphism: take the coproduct of a finite affine subcover of its Zariski affine cover. -/
private theorem exists_affine_surjective_localIso_cover
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : AlgebraicGeometry.BigFppfOver B S hS)
    [CompactSpace ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T)] :
    ∃ (U : AlgebraicGeometry.BigFppfOver B S hS) (v : U ⟶ T),
      IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U) ∧
      Surjective ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map v) ∧
      IsLocalIso ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map v) := by
  let G := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let V := (G.obj T).affineCover.finiteSubcover
  have hsize : B.Contains (∐ V.X) :=
    Scheme.size_sigmaObj_lt B.aleph0_lt_cutoff B.aleph0_lt_cutoff_cof
      Cardinal.mk_le_aleph0 V.X (fun i =>
        Scheme.size_lt_of_isOpenImmersion (V.f i) T.left.property)
  let U : AlgebraicGeometry.BigFppfOver B S hS :=
    Over.mk (Y := B.obj hsize) (ObjectProperty.homMk (Sigma.desc V.f ≫ T.hom.hom))
  let v : U ⟶ T := Over.homMk (ObjectProperty.homMk (Sigma.desc V.f)) rfl
  refine ⟨U, v, inferInstanceAs (IsAffine (∐ V.X)), ?_, ?_⟩
  · exact inferInstanceAs (Surjective (Sigma.desc V.f))
  · exact IsZariskiLocalAtSource.sigmaDesc (P := @IsLocalIso) (fun i =>
      ⟨fun x => ⟨⊤, trivial, inferInstance⟩⟩)

/-- A quasi-compact algebraic space has an affine surjective étale chart which is moreover a local
isomorphism whenever `X` is representable, by taking the chart to be an affine Zariski cover in
that case. This is the input for clause (3). -/
private theorem exists_affine_chart_localIso_of_representable
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (hqc : AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS X) :
    ∃ (U : AlgebraicGeometry.BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X),
      IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U) ∧
      (MorphismProperty.inverseImage (@Surjective.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf φ ∧
      AlgebraicGeometry.Space.IsEtale B S hS φ ∧
      (X.IsRepresentable → (MorphismProperty.inverseImage (@IsLocalIso.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf φ) := by
  classical
  by_cases hrep : X.IsRepresentable
  · let := hrep
    let G := AlgebraicGeometry.BigFppfOver.toScheme B S hS
    let T := X.reprX
    let e : yoneda.obj T ≅ X := X.reprW
    obtain ⟨W, ψ, hW, hψ, _⟩ := hqc
    let v : W ⟶ T := yoneda.preimage (ψ ≫ e.inv)
    have hv : yoneda.map v ≫ e.hom = ψ := by simp [v]
    have hp : IsPullback (𝟙 (yoneda.obj W)) (yoneda.map v) ψ e.hom :=
      IsPullback.of_horiz_isIso ⟨by simpa using hv.symm⟩
    let : CompactSpace (G.obj W) := hW
    let : Surjective (G.map v) := hψ.2 e.hom (𝟙 _) v hp
    let : CompactSpace (G.obj T) :=
      Function.Surjective.compactSpace (G.map v).continuous (Surjective.surj (f := G.map v))
    obtain ⟨U, f, hU, hfs, hfl⟩ := exists_affine_surjective_localIso_cover B S hS T
    let φ := yoneda.map f ≫ e.hom
    have hli : (MorphismProperty.inverseImage (@IsLocalIso.{u}) G).presheaf φ :=
      presheaf_yoneda_map_comp_iso B S hS _ f hfl e
    have hfe : Etale (G.map f) := by
      let : IsZariskiLocalAtSource (@Etale.{u}) :=
        HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Etale)
      let : MorphismProperty.ContainsIdentities (@Etale.{u}) :=
        (inferInstance : MorphismProperty.IsMultiplicative (@Etale.{u})).toContainsIdentities
      exact IsLocalIso.le_of_isZariskiLocalAtSource (@Etale.{u}) _ _ _ hfl
    refine ⟨U, φ, hU, ?_, ?_, fun _ => hli⟩
    · exact presheaf_yoneda_map_comp_iso B S hS _ f hfs e
    · exact AlgebraicGeometry.Space.isEtale_of_presheaf_etale B S hS
        (presheaf_yoneda_map_comp_iso B S hS _ f hfe e)
  · obtain ⟨U, φ, hU, hs, he⟩ := exists_affine_etale_surjective_chart B S hS X hX hqc
    exact ⟨U, φ, hU, hs, he, fun h => (hrep h).elim⟩

end ReasonableApproximation

attribute [local instance] ReasonableApproximation.schemeCutoff_isClosedUnderIsomorphisms
  ReasonableApproximation.schemeCutoff_isClosedUnderLimitsOfShape_walkingCospan
  ReasonableApproximation.schemeCutoff_hasTerminal
  ReasonableApproximation.schemeCutoff_hasPullbacks

open ReasonableApproximation in
/-- **Stacks 03K0.** A quasi-compact reasonable algebraic space over `S` is the colimit, in
sheaves, of a directed system of quasi-compact and quasi-separated algebraic spaces, and the
system can be arranged to satisfy clauses (1), (2) and (3) of the source. No quasi-separatedness
is assumed of `X`.

The system is the one of the source's proof, and it is not constant: by Stacks 03H6 write
`X = U/R` with `U` affine, and index the system by the quasi-compact open subschemes `R' ⊆ R`
which are still equivalence relations on `U`, ordered by inclusion. Reasonableness bounds the
degrees of the fibres of `U ⟶ X` by some `N` (Stacks 03JL), and that bound is what makes the
index set *cofinal in the quasi-compact opens of `R`* and hence directed: the chain of
composites `A ↦ c(A ×_{s, U, t} A)` out of a quasi-compact open `A` containing `e(U)`
stabilises at step `N`, because a chain of length exceeding `N` repeats a point in a fibre of
`U(k) ⟶ X(k)` for an algebraically closed `k` and can be shortened. Each stage `U/R'` is an
algebraic space by Stacks 02WW, and is quasi-separated by Stacks 07S4 because `R'` is
quasi-compact and `U` affine — whereas `R` itself is quasi-compact only when `X` is
quasi-separated, which is precisely when the system collapses to a single stage.

Clause (1) is the corrected one: injectivity of `colim X i(T) ⟶ X(T)` over every quasi-compact
test scheme `T`, surjectivity over the quasi-compact *quasi-separated* ones; see
`AlgebraicGeometry.Space.CorrectedDirectedApproximation`. Over all quasi-compact `T` the
surjectivity fails, by
`AlgebraicGeometry.Space.exists_quasiCompact_reasonable_isEmpty_directedApproximation`. -/
@[stacks 03K0 "clause (1) in the corrected form: the test schemes are the quasi-compact\
  quasi-separated ones, which is what the source's proof supports"]
theorem exists_correctedDirectedApproximation
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (hqc : AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS X)
    (hr : IsReasonableSpace B S hS X) :
    Nonempty (CorrectedDirectedApproximation B S hS hZ ⟨X, hX.isSheaf⟩) := by
  classical
  obtain ⟨U, φ, hU, hsurj, het, hφlocal⟩ :=
    exists_affine_chart_localIso_of_representable B S hS X hX hqc
  have hbounded := affine_etale_chart_has_bounded_fibers B S hS X hr U φ hU het
  obtain ⟨R, s, t, hR, heq, hs, ht, hRs, hRt⟩ :=
    exists_chart_etale_equivalence_relation B S hS X hX U φ het hbounded
  let : HasSheafify (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type u) :=
    BigFppfOver.hasSheafify_type B S hS
  let G := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let : IsAffine (G.obj U) := hU
  let : CompactSpace (G.obj U) := Scheme.compactSpace_of_isAffine _
  let : Etale (G.map s) := scheme_etale_of_isEtale_yoneda B S hS s hs
  let : Etale (G.map t) := scheme_etale_of_isEtale_yoneda B S hS t ht
  let EOver : EquivalenceRelation ((Over.post B.inclusion).map t)
      ((Over.post B.inclusion).map s) := heq.nonempty_equivalenceRelation.some
  let E : EquivalenceRelation (G.map t) (G.map s) := equivalenceRelation_forget EOver
  let P : (G.obj R).Opens → Prop := fun A => IsCompact (A : Set (G.obj R)) ∧
    IsEquivalenceRelation (A.ι ≫ G.map t) (A.ι ≫ G.map s)
  have hP (A : (G.obj R).Opens) (hA : IsCompact (A : Set (G.obj R))) :
      ∃ A', P A' ∧ A ≤ A' := by
    obtain ⟨A', hA', hAA', hEq⟩ :=
      exists_compact_open_subrelation_of_hasUniversallyBoundedFibers B S hS R U s t E hRs A hA
    exact ⟨A', ⟨hA', hEq⟩, hAA'⟩
  let I := {A : (G.obj R).Opens // P A}
  have hnonempty : Nonempty I := by
    obtain ⟨A, hA, _⟩ := hP ⊥ isCompact_empty
    exact ⟨⟨A, hA⟩⟩
  let : Nonempty I := hnonempty
  let : Category.{0} I := smallPreorderCategory I
  let : IsFiltered I := smallPreorderCategory_isFiltered I (by
    intro A A'
    obtain ⟨A'', hA, hA'⟩ := open_envelopes_directed P (fun A h => h.1) hP A A'
    exact ⟨A'', hA, hA'⟩)
  have hcover : (⨆ A : I, A.val) = ⊤ := open_envelopes_iSup_eq_top P hP
  let Y : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type u) := ⟨X, hX.isSheaf⟩
  let H := sheafOfSchemeFunctor B S hS
  let Ro : I ⥤ AlgebraicGeometry.BigFppfOver B S hS := {
    obj A := openObject B S hS R A.val
    map {A A'} f := openObjectMap B S hS R f.down
    map_id A := by
      apply Over.OverMorphism.ext
      apply ObjectProperty.hom_ext
      exact Scheme.homOfLE_rfl _ _
    map_comp f g := by
      apply Over.OverMorphism.ext
      apply ObjectProperty.hom_ext
      exact (Scheme.homOfLE_homOfLE R.left.obj f.down g.down).symm }
  let ι (A : I) := openObjectι B S hS R A.val
  have hι {A A' : I} (f : A ⟶ A') : Ro.map f ≫ ι A' = ι A :=
    openObjectMap_ι B S hS R f.down
  let RR := Ro ⋙ H
  let tt : RR ⟶ (Functor.const I).obj (H.obj U) := {
    app A := H.map (ι A ≫ t)
    naturality {A A'} f := by
      show H.map (Ro.map f) ≫ H.map (ι A' ≫ t) = H.map (ι A ≫ t) ≫ 𝟙 _
      rw [← H.map_comp, ← Category.assoc, hι, Category.comp_id] }
  let ss : RR ⟶ (Functor.const I).obj (H.obj U) := {
    app A := H.map (ι A ≫ s)
    naturality {A A'} f := by
      show H.map (Ro.map f) ≫ H.map (ι A' ≫ s) = H.map (ι A ≫ s) ≫ 𝟙 _
      rw [← H.map_comp, ← Category.assoc, hι, Category.comp_id] }
  let (A : I) : Stacks.Groupoids.IsEtaleEquivalenceRelation
      (relation B S hS (ι A ≫ s) (ι A ≫ t)) :=
    openObject_isEtaleEquivalenceRelation B S hS s t A.val A.property.2
  let Q (A : I) := Stacks.Groupoids.quotientSheaf (AlgebraicGeometry.BigFppfOver.topology B S hS)
    (Over.post B.inclusion) (relation B S hS (ι A ≫ s) (ι A ≫ t))
  let q (A : I) : H.obj U ⟶ Q A :=
    ⟨quotientMap B S hS (ι A ≫ s) (ι A ≫ t)⟩
  have hQ (A : I) : AlgebraicGeometry.IsAlgebraicSpace B S hS (Q A).obj :=
    isAlgebraicSpace_quotient_unconditional B S hS (ι A ≫ s) (ι A ≫ t)
  have hqsurj (A : I) : (MorphismProperty.inverseImage (@Surjective.{u}) G).presheaf
      (q A).hom := quotientMap_surjective_unconditional B S hS (ι A ≫ s) (ι A ≫ t)
  have hqet (A : I) : (MorphismProperty.inverseImage (@Etale.{u}) G).presheaf
      (q A).hom := quotientMap_etale_unconditional B S hS (ι A ≫ s) (ι A ≫ t)
  have hqpb (A : I) : IsPullback (tt.app A).hom (ss.app A).hom (q A).hom (q A).hom :=
    quotientMap_isPullback B S hS (ι A ≫ s) (ι A ≫ t)
  have hqw (A : I) : tt.app A ≫ q A = ss.app A ≫ q A := Sheaf.hom_ext (hqpb A).w
  have hqt (k : I) {W : AlgebraicGeometry.BigFppfOver B S hS} (a : W ⟶ Ro.obj k) (r : W ⟶ R)
      (ha : a ≫ ι k = r) (y z : W ⟶ U) (hy : r ≫ t = y) (hz : r ≫ s = z) :
      H.map y ≫ q k = H.map z ≫ q k := by
    subst ha hy hz
    rw [Category.assoc, Category.assoc, H.map_comp, H.map_comp, Category.assoc, Category.assoc]
    exact congrArg (H.map a ≫ ·) (hqw k)
  let hqcol (A : I) : IsColimit (Cofork.ofπ (q A) (hqw A)) :=
    sheafKernelPairIsColimit _ _ _ _ (hqpb A)
      (atlas_isLocallySurjective B S hS (Y := Q A) (q A).hom (hqsurj A) (hqet A))
  let p : H.obj U ⟶ Y := ⟨φ⟩
  have het' : (MorphismProperty.inverseImage (@Etale.{u}) G).presheaf φ := by
    apply het U (𝟙 _) (presheafProperty_id _ (fun {_ _} f hf => by
      let := hf
      show Etale (G.map f)
      infer_instance) _)
  have hpw : H.map t ≫ p = H.map s ≫ p := Sheaf.hom_ext hR.w
  let hpcol : IsColimit (Cofork.ofπ p hpw) :=
    sheafKernelPairIsColimit _ _ _ _ hR
      (atlas_isLocallySurjective B S hS (Y := Y) φ hsurj het')
  have hpi (A : I) : tt.app A ≫ p = ss.app A ≫ p := by
    show H.map (ι A ≫ t) ≫ p = H.map (ι A ≫ s) ≫ p
    rw [H.map_comp, H.map_comp, Category.assoc, Category.assoc, hpw]
  let D := quotientDiagram RR (H.obj U) tt ss Q q hqw hqcol
  let c := quotientCocone RR (H.obj U) tt ss Q q hqw hqcol p hpi
  have hqmap {A A' : I} (f : A ⟶ A') : q A ≫ D.map f = q A' :=
    quotientDiagram_map RR (H.obj U) tt ss Q q hqw hqcol f
  have hqι (A : I) : q A ≫ c.ι.app A = p :=
    quotientCocone_ι RR (H.obj U) tt ss Q q hqw hqcol p hpi A
  let hc : IsColimit c := quotientCoconeIsColimit RR (H.obj U) tt ss Q q hqw hqcol
    p (H.map t) (H.map s) hpw hpcol hpi (by
      intro Z a ha
      apply Sheaf.hom_ext
      apply sheaf_hom_ext_of_open_cover B S hS R (fun A : I => A.val) hcover Z
      intro A
      have h := congrArg (fun f => f.hom) (ha A)
      change yoneda.map (ι A ≫ t) ≫ a.hom = yoneda.map (ι A ≫ s) ≫ a.hom at h
      show yoneda.map (ι A) ≫ (yoneda.map t ≫ a.hom) =
        yoneda.map (ι A) ≫ (yoneda.map s ≫ a.hom)
      have h' : (yoneda.map (ι A) ≫ yoneda.map t) ≫ a.hom =
          (yoneda.map (ι A) ≫ yoneda.map s) ≫ a.hom := by
        simpa only [Functor.map_comp] using h
      exact (Category.assoc _ _ _).symm.trans (h'.trans (Category.assoc _ _ _)))
  have hqet' (A : I) : AlgebraicGeometry.Space.IsEtale B S hS (q A).hom :=
    AlgebraicGeometry.Space.isEtale_of_presheaf_etale B S hS (hqet A)
  have hqsurj' (A : I) : IsSurjective B S hS (q A).hom :=
    atlas_isSurjective B S hS (hQ A) _ (hqsurj A)
  have hpet (A : I) : AlgebraicGeometry.Space.IsEtale B S hS (c.ι.app A).hom :=
    AlgebraicGeometry.Space.isEtale_of_comp_surjective_isEtale B S hS
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U) (hQ A) hX
      (q A).hom φ (c.ι.app A).hom
      (congrArg (fun f => f.hom) (hqι A)).symm (hqsurj' A) (hqet' A) het
  have hdEt (A A' : I) (f : A ⟶ A') : AlgebraicGeometry.Space.IsEtale B S hS (D.map f).hom :=
    AlgebraicGeometry.Space.isEtale_of_comp_surjective_isEtale B S hS
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U) (hQ A) (hQ A')
      (q A).hom (q A').hom (D.map f).hom
      (congrArg (fun f => f.hom) (hqmap f)).symm (hqsurj' A) (hqet' A) (hqet' A')
  have hsurj_of_comp (A : I) {Z : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type u)}
      (g : Q A ⟶ Z) (h : IsSurjective B S hS (q A ≫ g).hom) : IsSurjective B S hS g.hom := by
    refine Function.Surjective.of_comp (g := pointsMap B S hS _ (q A).hom) ?_
    rw [← pointsMap_comp]
    exact h
  have hdSurj (A A' : I) (f : A ⟶ A') : IsSurjective B S hS (D.map f).hom :=
    hsurj_of_comp A _ (by rw [hqmap]; exact hqsurj' A')
  have hpSurj (A : I) : IsSurjective B S hS (c.ι.app A).hom :=
    hsurj_of_comp A _ (by rw [hqι]; exact atlas_isSurjective B S hS hX φ hsurj)
  have hqcqs (A : I) : AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS (Q A).obj ∧
      AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated B S hS hZ (Q A).obj := by
    let : CompactSpace (G.obj (Ro.obj A)) := isCompact_iff_compactSpace.mp A.property.1
    let : Etale (G.map (ι A ≫ t)) := inferInstanceAs (Etale (A.val.ι ≫ G.map t))
    let : Etale (G.map (ι A ≫ s)) := inferInstanceAs (Etale (A.val.ι ≫ G.map s))
    apply quotient_is_quasiCompact_quasiSeparated B S hS hZ U (Ro.obj A)
      (ι A ≫ t) (ι A ≫ s) hU inferInstance
    · exact ⟨⟨equivalenceRelation_over A.property.2.nonempty_equivalenceRelation.some⟩⟩
    · exact isEtale_yoneda_of_scheme_etale B S hS _
    · exact isEtale_yoneda_of_scheme_etale B S hS _
  have hsectionsSurj (T : AlgebraicGeometry.BigFppfOver B S hS)
      (hTc : CompactSpace (G.obj T)) (hTqs : QuasiSeparatedSpace (G.obj T))
      (ξ : X.obj (op T)) : ∃ (A : I) (η : (Q A).obj.obj (op T)),
        ((c.ι.app A).hom.app (op T) η : X.obj (op T)) = ξ := by
    let := hTc
    let := hTqs
    let ξ' : yoneda.obj T ⟶ X := yonedaEquiv.symm ξ
    obtain ⟨W, v, w, hW, hvSurj, hvEt, hw⟩ :=
      exists_compact_etale_lift B S hS φ hsurj het' ξ'
    let := hW
    let := hvSurj
    let := hvEt
    let : CompactSpace (G.obj (pullback v v)) :=
      compactSpace_pullback_of_compact_of_quasiSeparated B S hS v
    have hwrel : yoneda.map (pullback.fst v v ≫ w) ≫ φ =
        yoneda.map (pullback.snd v v ≫ w) ≫ φ := by
      simp only [Functor.map_comp, Category.assoc, hw]
      rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp,
        ← Functor.map_comp, pullback.condition]
    obtain ⟨r, hr⟩ := exists_lift_of_isPullback_yoneda φ t s hR (pullback.fst v v ≫ w)
      (pullback.snd v v ≫ w) hwrel
    obtain ⟨A, hA, g, hg⟩ := exists_factorization_through_site_open_envelope B S hS r P hP
    let k : I := ⟨A, hA⟩
    have hwq : H.map (pullback.fst v v) ≫ (H.map w ≫ q k) =
        H.map (pullback.snd v v) ≫ (H.map w ≫ q k) := by
      rw [← Category.assoc, ← Category.assoc, ← H.map_comp, ← H.map_comp]
      exact hqt k g r hg _ _ hr.1 hr.2
    let hvcol := sheafIsColimitOfSurjectiveEtale B S hS v
    let d : H.obj T ⟶ Q k := Cofork.IsColimit.desc hvcol (H.map w ≫ q k) hwq
    have hd : H.map v ≫ d = H.map w ≫ q k := Cofork.IsColimit.π_desc' hvcol _ _
    have hdp : d ≫ c.ι.app k = (⟨ξ'⟩ : H.obj T ⟶ Y) := by
      apply Cofork.IsColimit.hom_ext hvcol
      show H.map v ≫ (d ≫ c.ι.app k) = H.map v ≫ (⟨ξ'⟩ : H.obj T ⟶ Y)
      rw [← Category.assoc, hd, Category.assoc, hqι]
      exact Sheaf.hom_ext hw
    refine ⟨k, d.hom.app (op T) (𝟙 T), ?_⟩
    exact (congrArg (fun f : H.obj T ⟶ Y => yonedaEquiv f.hom) hdp).trans
      (yonedaEquiv.apply_symm_apply ξ)
  have hsectionsInj (T : AlgebraicGeometry.BigFppfOver B S hS)
      (hTc : CompactSpace (G.obj T)) (i j : I)
      (η : (Q i).obj.obj (op T)) (θ : (Q j).obj.obj (op T))
      (heq : (c.ι.app i).hom.app (op T) η = (c.ι.app j).hom.app (op T) θ) :
      ∃ (k : I) (f : i ⟶ k) (g : j ⟶ k),
        (D.map f).hom.app (op T) η = (D.map g).hom.app (op T) θ := by
    let := hTc
    let η' : H.obj T ⟶ Q i := ⟨yonedaEquiv.symm η⟩
    let θ' : H.obj T ⟶ Q j := ⟨yonedaEquiv.symm θ⟩
    have heq' : η' ≫ c.ι.app i = θ' ≫ c.ι.app j := by
      apply Sheaf.hom_ext
      apply yonedaEquiv.injective
      show yonedaEquiv (yonedaEquiv.symm η ≫ (c.ι.app i).hom) =
        yonedaEquiv (yonedaEquiv.symm θ ≫ (c.ι.app j).hom)
      rwa [yonedaEquiv_comp, yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    obtain ⟨W₁, v₁, w₁, hW₁, hv₁s, hv₁e, hw₁⟩ :=
      exists_compact_etale_lift B S hS (q i).hom (hqsurj i) (hqet i) η'.hom
    let := hW₁
    let := hv₁s
    let := hv₁e
    obtain ⟨W₂, v₂, w₂, hW₂, hv₂s, hv₂e, hw₂⟩ :=
      exists_compact_etale_lift B S hS (q j).hom (hqsurj j) (hqet j)
        (yoneda.map v₁ ≫ θ'.hom)
    let := hW₂
    let := hv₂s
    let := hv₂e
    let v := v₂ ≫ v₁
    let y := v₂ ≫ w₁
    have hy : H.map y ≫ q i = H.map v ≫ η' := by
      apply Sheaf.hom_ext
      show yoneda.map (v₂ ≫ w₁) ≫ (q i).hom = yoneda.map (v₂ ≫ v₁) ≫ η'.hom
      rw [yoneda.map_comp, yoneda.map_comp, Category.assoc, Category.assoc, hw₁]
    have hz : H.map w₂ ≫ q j = H.map v ≫ θ' := by
      apply Sheaf.hom_ext
      show yoneda.map w₂ ≫ (q j).hom = yoneda.map (v₂ ≫ v₁) ≫ θ'.hom
      rwa [yoneda.map_comp, Category.assoc]
    have hyz : yoneda.map y ≫ φ = yoneda.map w₂ ≫ φ := by
      show (H.map y ≫ p).hom = (H.map w₂ ≫ p).hom
      congr 1
      calc
        H.map y ≫ p = H.map y ≫ (q i ≫ c.ι.app i) := congrArg _ (hqι i).symm
        _ = (H.map v ≫ η') ≫ c.ι.app i := by rw [← Category.assoc, hy]
        _ = (H.map v ≫ θ') ≫ c.ι.app j := by rw [Category.assoc, heq', ← Category.assoc]
        _ = H.map w₂ ≫ p := by rw [← hz, Category.assoc, hqι]
    obtain ⟨r, hr⟩ := exists_lift_of_isPullback_yoneda φ t s hR y w₂ hyz
    obtain ⟨A, hA, a, ha⟩ := exists_factorization_through_site_open_envelope B S hS r P hP
    obtain ⟨k₀, fi, fj, _⟩ := IsFilteredOrEmpty.cocone_objs i j
    obtain ⟨k, fa, fk, _⟩ := IsFilteredOrEmpty.cocone_objs (⟨A, hA⟩ : I) k₀
    let a' := a ≫ Ro.map fa
    have ha' : a' ≫ ι k = r := by
      dsimp only [a']
      rwa [Category.assoc, hι]
    have hqyz : H.map y ≫ q k = H.map w₂ ≫ q k := hqt k a' r ha' y w₂ hr.1 hr.2
    have hresult : η' ≫ D.map (fi ≫ fk) = θ' ≫ D.map (fj ≫ fk) := by
      let : Surjective (G.map v) := inferInstanceAs (Surjective (G.map v₂ ≫ G.map v₁))
      let : Etale (G.map v) := inferInstanceAs (Etale (G.map v₂ ≫ G.map v₁))
      apply Cofork.IsColimit.hom_ext (sheafIsColimitOfSurjectiveEtale B S hS v)
      show H.map v ≫ (η' ≫ D.map (fi ≫ fk)) = H.map v ≫ (θ' ≫ D.map (fj ≫ fk))
      rwa [← Category.assoc, ← Category.assoc, ← hy, ← hz, Category.assoc, Category.assoc,
        hqmap, hqmap]
    refine ⟨k, fi ≫ fk, fj ≫ fk, ?_⟩
    have h := congrArg (fun f : H.obj T ⟶ Q k => yonedaEquiv f.hom) hresult
    change yonedaEquiv (yonedaEquiv.symm η ≫ (D.map (fi ≫ fk)).hom) =
      yonedaEquiv (yonedaEquiv.symm θ ≫ (D.map (fj ≫ fk)).hom) at h
    rwa [yonedaEquiv_comp, yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
  have hscheme (hrep : X.IsRepresentable) (A : I) : (Q A).obj.IsRepresentable ∧
      (MorphismProperty.inverseImage (@IsLocalIso.{u}) G).presheaf (c.ι.app A).hom ∧
      (MorphismProperty.inverseImage (@IsLocalIso.{u}) G).presheaf (q A).hom :=
    isRepresentable_and_localIso_of_localIso_atlas B S hS (hQ A) φ (q A).hom
      (c.ι.app A).hom (congrArg (fun f => f.hom) (hqι A))
      (hφlocal hrep) (hqet A) (hqsurj A) hrep
  have hschemeTransition (hrep : X.IsRepresentable) (i j : I) (f : i ⟶ j) :
      (MorphismProperty.inverseImage (@IsLocalIso.{u}) G).presheaf (D.map f).hom :=
    (isRepresentable_and_localIso_of_localIso_atlas B S hS (hQ i)
      (q j).hom (q i).hom (D.map f).hom (congrArg (fun f => f.hom) (hqmap f))
      (hscheme hrep j).2.2 (hqet i) (hqsurj i) (hscheme hrep j).1).2.1
  have hιid (A : I) : c.ι.app A ≫ 𝟙 Y = c.ι.app A := Category.comp_id _
  refine ⟨{
    index := Cat.of I
    filtered := (inferInstance : IsFiltered I)
    thin := fun _ _ => ⟨fun ⟨_⟩ ⟨_⟩ => rfl⟩
    diagram := D
    cocone := c
    comparison := Iso.refl Y
    isColimit := hc
    algebraicSpace := hQ
    quasiCompact := fun A => (hqcqs A).1
    quasiSeparated := fun A => (hqcqs A).2
    sections_surjective := ?_
    sections_eventually_injective := ?_
    transition_surjective := hdSurj
    transition_etale := hdEt
    projection_surjective := ?_
    projection_etale := ?_
    scheme_stages := fun hrep A => (hscheme hrep A).1
    scheme_transition_localIso := hschemeTransition
    scheme_projection_localIso := ?_ }⟩
  · intro T hTc hTqs ξ
    obtain ⟨A, η, hη⟩ := hsectionsSurj T hTc hTqs ξ
    refine ⟨A, η, ?_⟩
    simp only [Iso.refl_hom, hιid]
    exact hη
  · intro T hTc i j η θ heq
    simp only [Iso.refl_hom, hιid] at heq
    exact hsectionsInj T hTc i j η θ heq
  · intro A
    simpa only [Iso.refl_hom, hιid] using hpSurj A
  · intro A
    simpa only [Iso.refl_hom, hιid] using hpet A
  · intro hrep A
    simpa only [Iso.refl_hom, hιid] using (hscheme hrep A).2.1

end AlgebraicGeometry.Space

end
