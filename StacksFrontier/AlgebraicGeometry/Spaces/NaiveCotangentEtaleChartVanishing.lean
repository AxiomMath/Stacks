module

public import StacksFrontier.AlgebraicGeometry.Spaces.NaiveCotangentEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPushforward

/-!
# Vanishing of `H⁻¹(NL_{X/Y})` on a surjective étale chart

Let `p ≫ f = g ≫ q` be a commuting square of morphisms of algebraic spaces over a scheme `S`,
with `p` and `q` étale, `p` surjective, and the source of `p` the algebraic space of a scheme of
the site. The cohomology sheaf `H⁻¹` of the naive cotangent complex `NL_{X/Y}` of Stacks 0D0V
vanishes exactly when `H⁻¹(NL_{U/V})` does.

Both complexes are concentrated in degrees `-1` and `0`, so the vanishing of `H⁻¹` is the
injectivity of the differential out of degree `-1`. Restriction of `𝒪_X`-modules to the small
étale site of `U` detects monomorphisms when `p` is surjective, sections over a chart of `X`
injecting into sections over its base change along `p`, and it carries `NL_{X/Y}` to `NL_{U/V}`
by Stacks 0D0W, `AlgebraicGeometry.Space.naiveCotangentEtaleRestrictionIso`.

## Main results

* `HomologicalComplex.isZero_homology_negOne_iff_mono_d`: for a cochain complex with a zero
  object in degree `-2`, `H⁻¹ = 0` if and only if the differential out of degree `-1` is a
  monomorphism.
* `AlgebraicGeometry.Space.mono_iff_mono_etaleModuleRestriction_map`: restriction to a surjective
  étale scheme chart detects monomorphisms.
* `AlgebraicGeometry.Space.isZero_homology_negOne_naiveCotangentComplex_iff_of_etale_surjective`:
  `H⁻¹(NL_{X/Y}) = 0` if and only if `H⁻¹(NL_{U/V}) = 0`.

## References

* [Stacks Project, Tag 0D0W](https://stacks.math.columbia.edu/tag/0D0W)
* [Stacks Project, Tag 0D12](https://stacks.math.columbia.edu/tag/0D12)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w m

namespace HomologicalComplex

/-- In a cochain complex with a zero object in degree `-2`, the cohomology in degree `-1`
vanishes exactly when the differential out of degree `-1` is a monomorphism. -/
theorem isZero_homology_negOne_iff_mono_d {C : Type*} [Category C] [Abelian C]
    (K : CochainComplex C ℤ) (hK : IsZero (K.X (-2))) :
    IsZero (K.homology (-1)) ↔ Mono (K.d (-1) 0) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ (-2) (-1) 0 (by simp) (by simp)]
  exact ShortComplex.exact_iff_mono _ (hK.eq_of_src _ _)

end HomologicalComplex

namespace Stacks.SheafOfModules

/-- A morphism of sheaves of modules is a monomorphism exactly when it is injective on the
sections over every object. -/
theorem mono_iff_forall_injective_val_app {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat} {F G : _root_.SheafOfModules R} (d : F ⟶ G) :
    Mono d ↔ ∀ V, Function.Injective (d.val.app V) := by
  refine ⟨fun _ ↦ ?_, fun h ↦ (_root_.SheafOfModules.forget _).mono_of_mono_map
    (PresheafOfModules.mono_of_injective h)⟩
  have : Mono d.val := (_root_.SheafOfModules.forget _).map_mono d
  exact PresheafOfModules.injective_of_mono _

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Space

attribute [local instance 1] Sheaf.hasWeakSheafifyCommRingCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Restriction of sections of a sheaf of modules on the small étale site of an algebraic space,
over any sheaf of rings, along a morphism of étale charts whose underlying morphism of schemes
is surjective and étale is injective: such a morphism generates a covering sieve. -/
theorem injective_sheafOfModules_val_map_of_etale_surjective (X : AlgebraicSpaces B S hS)
    {R : Sheaf (SmallEtale.topology B S hS X.1) RingCat.{w}}
    (G : _root_.SheafOfModules.{m} R) {V W : SmallEtale B S hS X.1} (k : W ⟶ V)
    (hk : Etale ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).map k))
    (hs : Surjective ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).map k)) :
    Function.Injective (G.val.map k.op) := by
  have hpre : Presieve.singleton k ∈ SmallEtale.precoverage B S hS X.1 V := by
    rw [SmallEtale.precoverage_eq_comap, Precoverage.mem_comap_iff, Presieve.map_singleton]
    exact B.singleton_mem_etalePrecoverage _ hs hk
  have hcov : Sieve.generate (Presieve.singleton k) ∈ SmallEtale.topology B S hS X.1 V :=
    Precoverage.generate_mem_toGrothendieck hpre
  intro x y h
  refine G.isSheaf.isSeparated V _ hcov x y ?_
  rintro Z _ ⟨T, c, _, ⟨⟩, rfl⟩
  have e : ∀ z, G.val.presheaf.map (c ≫ k).op z
      = G.val.presheaf.map c.op (G.val.presheaf.map k.op z) := fun z =>
    PresheafOfModules.map_comp_apply _ _ _ z
  exact (e x).trans ((congrArg (G.val.presheaf.map c.op) h).trans (e y).symm)

/-- The restriction of a morphism `d` of `𝒪_X`-modules along an étale `i : U ⟶ X` acts on the
sections over a chart `W` of `U` as `d` acts on the sections over the image of `W` in `X`. -/
theorem etaleModuleRestriction_map_val_app {X U : AlgebraicSpaces B S hS} (i : U ⟶ X)
    (hi : IsEtale B S hS i.hom)
    {F G : _root_.SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u} (smallEtaleRingedTopos B S hS X).O)}
    (d : F ⟶ G) (W : (SmallEtale B S hS U.1)ᵒᵖ)
    (x : F.val.obj (op ((smallEtalePostcomp B S hS i hi).obj W.unop))) :
    ((etaleModuleRestriction B S hS i hi).map d).val.app W x =
      d.val.app (op ((smallEtalePostcomp B S hS i hi).obj W.unop)) x := rfl

/-- If restriction along an étale `i : U ⟶ X` makes a morphism of `𝒪_X`-modules injective on
the sections over a chart `W` of `U`, and the image of `W` in `X` maps to `V` by a surjective
étale morphism, the morphism is injective on the sections over `V`. -/
theorem injective_val_app_of_etaleModuleRestriction {X U : AlgebraicSpaces B S hS} (i : U ⟶ X)
    (hi : IsEtale B S hS i.hom)
    {F G : _root_.SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u} (smallEtaleRingedTopos B S hS X).O)}
    (d : F ⟶ G) (W : SmallEtale B S hS U.1) (V : SmallEtale B S hS X.1)
    (k : (smallEtalePostcomp B S hS i hi).obj W ⟶ V)
    (hk : Etale ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).map k))
    (hs : Surjective ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).map k))
    (h : Function.Injective (((etaleModuleRestriction B S hS i hi).map d).val.app (op W))) :
    Function.Injective (d.val.app (op V)) := by
  intro s t hst
  apply injective_sheafOfModules_val_map_of_etale_surjective B S hS X F k hk hs
  have h1 := etaleModuleRestriction_map_val_app B S hS i hi d (op W) (F.val.map k.op s)
  have h2 := etaleModuleRestriction_map_val_app B S hS i hi d (op W) (F.val.map k.op t)
  refine h (h1.trans (Eq.trans ?_ h2.symm))
  rw [PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply, hst]

/-- **Restriction to a surjective étale scheme chart detects monomorphisms** of sheaves of
`𝒪_X`-modules: a morphism is injective on all sections as soon as it is so on the sections over
the charts of the form `W ⟶ U ⟶ X`. -/
theorem mono_iff_mono_etaleModuleRestriction_map {X : AlgebraicSpaces B S hS}
    (U : BigFppfOver B S hS) (i : schemeSpace U ⟶ X) (hi : IsEtale B S hS i.hom)
    (hs : (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf i.hom)
    {F G : _root_.SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u} (smallEtaleRingedTopos B S hS X).O)}
    (d : F ⟶ G) :
    Mono d ↔ Mono ((etaleModuleRestriction B S hS i hi).map d) := by
  rw [Stacks.SheafOfModules.mono_iff_forall_injective_val_app,
    Stacks.SheafOfModules.mono_iff_forall_injective_val_app]
  refine ⟨fun h W ↦ h (op ((smallEtalePostcomp B S hS i hi).obj W.unop)), fun h V ↦ ?_⟩
  let T := BigFppfOver.toScheme B S hS
  let P := MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u}) T
  have hi' : P.presheaf i.hom := (isEtale_iff_presheaf_of_yoneda B S hS i.hom).1 hi
  let r := hs.rep
  let p := r.fst' V.unop.1.hom
  let q := r.snd V.unop.1.hom
  have sq := r.isPullback' V.unop.1.hom
  have hp : P p := V.unop.2.property i.hom (yoneda.map q) p sq.flip
  have hq : Etale (T.map q) := hi'.property V.unop.1.hom (yoneda.map p) q sq
  have hqs : Surjective (T.map q) := hs.property V.unop.1.hom (yoneda.map p) q sq
  let W : SmallEtale B S hS (schemeSpace U).1 :=
    ⟨CostructuredArrow.mk (yoneda.map p), (presheaf_yoneda_map_etale_iff B S hS p).2 hp⟩
  let k : (smallEtalePostcomp B S hS i hi).obj W ⟶ V.unop := ⟨CostructuredArrow.homMk q sq.w.symm⟩
  exact injective_val_app_of_etaleModuleRestriction B S hS i hi d W V.unop k hq hqs (h (op W))

/-- The naive cotangent complex of a morphism of algebraic spaces vanishes in degree `-2`. -/
theorem isZero_naiveCotangentComplex_X_negTwo {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    IsZero ((naiveCotangentComplex B S hS f).X (-2)) :=
  Stacks.SheafOfModules.naiveCotangentComplex_isZero_X.{u, u + 1, u, u}
    (smallEtaleRingedTopos B S hS X).J _ _ _ (-2) (by decide) (by decide)

/-- **Vanishing of `H⁻¹(NL_{X/Y})` is read on a surjective étale scheme chart.** For a
commuting square `p ≫ f = g ≫ q` of algebraic spaces over `S` with `p` and `q` étale, `p`
surjective and the source of `p` the algebraic space of a scheme of the site,
`H⁻¹(NL_{X/Y}) = 0` exactly when `H⁻¹(NL_{U/V}) = 0`. Both complexes vanish in degree `-2`, so
the condition is that the differential out of degree `-1` be a monomorphism; restriction to
`U_étale` detects monomorphisms, and carries `NL_{X/Y}` to `NL_{U/V}` (Stacks 0D0W). -/
theorem isZero_homology_negOne_naiveCotangentComplex_iff_of_etale_surjective
    {X Y V : AlgebraicSpaces B S hS} (U : BigFppfOver B S hS) {p : schemeSpace U ⟶ X}
    {f : X ⟶ Y} {g : schemeSpace U ⟶ V} {q : V ⟶ Y} (h : p ≫ f = g ≫ q)
    (hp : IsEtale B S hS p.hom) (hq : IsEtale B S hS q.hom)
    (hs : (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p.hom) :
    IsZero ((naiveCotangentComplex B S hS f).homology (-1)) ↔
      IsZero ((naiveCotangentComplex B S hS g).homology (-1)) := by
  let R := etaleModuleRestriction B S hS p hp
  let K := (R.mapHomologicalComplex (ComplexShape.up ℤ)).obj (naiveCotangentComplex B S hS f)
  rw [HomologicalComplex.isZero_homology_negOne_iff_mono_d _
      (isZero_naiveCotangentComplex_X_negTwo B S hS f),
    mono_iff_mono_etaleModuleRestriction_map B S hS U p hp hs]
  exact (HomologicalComplex.isZero_homology_negOne_iff_mono_d K
      (R.map_isZero (isZero_naiveCotangentComplex_X_negTwo B S hS f))).symm.trans
    (HomologicalComplex.homologyMapIso (naiveCotangentEtaleRestrictionIso B S hS h hp hq)
      (-1)).isZero_iff

end AlgebraicGeometry.Space

end
