module

public import StacksFrontier.RingTheory.Tor.BaseChange

/-!
# Flat base change for Tor over rings in an arbitrary universe

Let `S -> S'` be a flat ring map of commutative rings in an arbitrary universe `u`, and let `M`,
`N` be `S`-modules. Then for every `i >= 0` the natural base-change map
`Tor_i^S(M, N) (x)_S S' -> Tor_i^{S'}(M (x)_S S', N (x)_S S')` is an isomorphism of
`S'`-modules (Stacks Tag `00M8`).

`StacksFrontier.RingTheory.Tor.BaseChange` proves this for rings in `Type`; the statements here are
the same ones for rings in `Type u`, under names carrying the suffix `OfUniverse`, which is what
a consumer indexed by a scheme universe needs, the stalks of a scheme `X : Scheme.{u}` being
rings in `Type u`. The construction is the one of that module: base change is
`ModuleCat.extendScalars (algebraMap S S')`, and flatness enters only through
`torBaseChangeHomologyIsoOfUniverse` and through base change of a projective resolution
remaining a resolution.

## Main results

* `torBaseChangeIsoOfUniverse`: the base-change comparison
  `Tor_i^S(M, N) (x)_S S' ≅ Tor_i^{S'}(M (x)_S S', N (x)_S S')`.
* `flat_base_change_tor_of_universe`: **Tag 00M8**, its underlying morphism is an isomorphism.
-/

@[expose] public section

open CategoryTheory MonoidalCategory

section OfUniverse

universe u

variable {S S' : Type u} [CommRing S] [CommRing S'] [Algebra S S']

/-- Base change of `S`-modules along `S -> S'`, i.e. the functor `- (x)_S S'`, for rings in an
arbitrary universe. -/
noncomputable abbrev torBaseChangeOfUniverse : ModuleCat.{u} S ⥤ ModuleCat.{u} S' :=
  ModuleCat.extendScalars (algebraMap S S')

/-- Base change is an additive functor. -/
noncomputable instance torBaseChangeOfUniverse_additive :
    (torBaseChangeOfUniverse (S := S) (S' := S')).Additive :=
  (ModuleCat.extendRestrictScalarsAdj (algebraMap S S')).left_adjoint_additive

/-- When `S'` is flat over `S`, base change preserves finite limits. -/
noncomputable instance torBaseChangeOfUniverse_preservesFiniteLimits [Module.Flat S S'] :
    Limits.PreservesFiniteLimits (torBaseChangeOfUniverse (S := S) (S' := S')) :=
  ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (RingHom.flat_algebraMap_iff.mpr ‹_›)

/-- When `S'` is flat over `S`, base change is exact, hence preserves homology. -/
noncomputable instance torBaseChangeOfUniverse_preservesHomology [Module.Flat S S'] :
    (torBaseChangeOfUniverse (S := S) (S' := S')).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

/-- Base change sends projective modules to projective modules. -/
noncomputable instance torBaseChangeOfUniverse_preservesProjectives :
    (torBaseChangeOfUniverse (S := S) (S' := S')).PreservesProjectiveObjects :=
  Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
    (ModuleCat.extendRestrictScalarsAdj (algebraMap S S'))

/-- The monoidal comparison natural isomorphism for base change:
`e (M (x) -) ≅ (e M) (x) (e -)`, i.e. base change commutes with the tensor
product `(M (x)_S X) (x)_S S' ≅ (M (x)_S S') (x)_{S'} (X (x)_S S')`. -/
noncomputable def torBaseChangeTensorIsoOfUniverse (M : ModuleCat.{u} S) :
    (MonoidalCategory.tensorLeft M) ⋙ torBaseChangeOfUniverse (S := S) (S' := S') ≅
      torBaseChangeOfUniverse (S := S) (S' := S') ⋙
        MonoidalCategory.tensorLeft
          ((torBaseChangeOfUniverse (S := S) (S' := S')).obj M) :=
  NatIso.ofComponents
    (fun X => (asIso (Functor.LaxMonoidal.μ
      (ModuleCat.extendScalars (algebraMap S S')) M X)).symm)
    (by
      intro X Y f
      dsimp
      rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
      exact (Functor.LaxMonoidal.μ_natural_right
        (ModuleCat.extendScalars (algebraMap S S')) M f).symm)

/-- For flat `S'`, base change commutes with homology: `e (H_n K) ≅ H_n (e K)`. -/
noncomputable def torBaseChangeHomologyIsoOfUniverse [Module.Flat S S']
    (K : HomologicalComplex (ModuleCat.{u} S) (ComplexShape.down ℕ)) (n : ℕ) :
    (torBaseChangeOfUniverse (S := S) (S' := S')).obj (K.homology n) ≅
      (((torBaseChangeOfUniverse (S := S) (S' := S')).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj K).homology n :=
  (ShortComplex.mapHomologyIso (K.sc n)
      (torBaseChangeOfUniverse (S := S) (S' := S'))).symm ≪≫
    HomologicalComplex.homologyMapIso
      (Iso.refl (((torBaseChangeOfUniverse (S := S) (S' := S')).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj K)) n

/-- The canonical base-change comparison isomorphism between the official Tor objects,
`Tor_i^S(M, N) (x)_S S' ≅ Tor_i^{S'}(M (x)_S S', N (x)_S S')`, built from the chosen projective
resolution of `N`, for rings in an arbitrary universe. -/
noncomputable def torBaseChangeIsoOfUniverse [Module.Flat S S'] (i : ℕ)
    (M N : ModuleCat.{u} S) :
    (torBaseChangeOfUniverse (S := S) (S' := S')).obj
        (((Tor (ModuleCat.{u} S) i).obj M).obj N) ≅
      ((Tor (ModuleCat.{u} S') i).obj
          ((torBaseChangeOfUniverse (S := S) (S' := S')).obj M)).obj
        ((torBaseChangeOfUniverse (S := S) (S' := S')).obj N) := by
  let P : ProjectiveResolution N := ProjectiveResolution.of N
  let cs := ComplexShape.down ℕ
  let T := MonoidalCategory.tensorLeft M
  let T' := MonoidalCategory.tensorLeft
    ((torBaseChangeOfUniverse (S := S) (S' := S')).obj M)
  -- Step 1: apply base change to `Tor_i^S(M,N) ≅ H_i((M (x) -) P)`.
  refine (torBaseChangeOfUniverse (S := S) (S' := S')).mapIso
    (P.isoLeftDerivedObj T i) ≪≫ ?_
  -- Step 2: base change commutes with homology (uses flatness).
  refine torBaseChangeHomologyIsoOfUniverse ((T.mapHomologicalComplex cs).obj P.complex) i ≪≫ ?_
  -- Step 3: monoidal identification of the base-changed complex.
  refine (HomologicalComplex.homologyMapIso
    ((NatIso.mapHomologicalComplex (torBaseChangeTensorIsoOfUniverse M) cs).app
      P.complex) i) ≪≫ ?_
  -- Step 4: base change of `P` is a resolution of `e N`, computing `Tor^{S'}`.
  exact (ProjectiveResolution.isoLeftDerivedObj
    ((torBaseChangeOfUniverse (S := S) (S' := S')).mapProjectiveResolution P) T' i).symm

variable (S') in
/-- **Flat base change for Tor** (Stacks Tag `00M8`), for rings in an arbitrary universe.

Let `S -> S'` be a flat ring map of commutative rings (encoded as an `S`-algebra `S'` with
`Module.Flat S S'`), and let `M`, `N` be `S`-modules. Then for every `i` the canonical
base-change map `Tor_i^S(M, N) (x)_S S' -> Tor_i^{S'}(M (x)_S S', N (x)_S S')` — the underlying
morphism `(torBaseChangeIsoOfUniverse i M N).hom` of the comparison — is an isomorphism of
`S'`-modules. -/
@[stacks 00M8]
theorem flat_base_change_tor_of_universe [Module.Flat S S'] (i : ℕ) (M N : ModuleCat.{u} S) :
    IsIso (torBaseChangeIsoOfUniverse (S' := S') i M N).hom :=
  inferInstance

end OfUniverse
