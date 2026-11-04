module

public import Mathlib.CategoryTheory.Extensive
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.AffineCoversTop
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.Limits
public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.SmallToBigTopos

/-!
# Finite disjoint unions in the small pro-étale site

Let `B` be a chosen big pro-étale site containing a scheme `S`. A finite disjoint union of
schemes weakly étale over `S` and lying in `B` is again weakly étale over `S` and lies in `B`, so
the small pro-étale site of `S` has finite coproducts, computed on underlying schemes. Since it
also has the fibre products of schemes, it is finitary extensive: finite coproducts in it are
disjoint and universal. The summands of a finite disjoint union form a Zariski covering of it, so
they cover it in the pro-étale topology.

## Main results

* `AlgebraicGeometry.ProEtale.SmallProetale.hasFiniteCoproducts` and
  `AlgebraicGeometry.ProEtale.SmallProetale.toScheme_preservesFiniteCoproducts`: the small
  pro-étale site has finite coproducts, computed on underlying schemes.
* `AlgebraicGeometry.ProEtale.SmallProetale.finitaryExtensive`: the small pro-étale site is
  finitary extensive.
* `AlgebraicGeometry.ProEtale.SmallProetale.ofArrows_mem_topology_of_isColimit`: the summands of
  a finite disjoint union in the small pro-étale site cover it.

## References

* [Stacks Project, Tag 098M](https://stacks.math.columbia.edu/tag/098M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry

/-- The summands of a finite disjoint union of schemes form a Zariski covering of it. -/
theorem Scheme.ofArrows_mem_zariskiPrecoverage_of_isColimit {ι : Type w} [Finite ι]
    {Y : ι → Scheme.{u}} (c : Cofan Y) (hc : IsColimit c) :
    Presieve.ofArrows Y c.inj ∈ Scheme.zariskiPrecoverage c.pt := by
  let e : (∐ Y) ≅ c.pt := (coproductIsCoproduct Y).coconePointUniqueUpToIso hc
  have h := ((sigmaOpenCover Y).pushforwardIso e.hom).mem₀
  have he (j : ι) : Sigma.ι Y j ≫ e.hom = c.inj j :=
    (coproductIsCoproduct Y).comp_coconePointUniqueUpToIso_hom hc ⟨j⟩
  change Presieve.ofArrows Y (fun j ↦ Sigma.ι Y j ≫ e.hom) ∈
    Scheme.zariskiPrecoverage c.pt at h
  simpa only [he] using h

namespace ProEtale

variable (B : BigProetaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace SmallProetale

/-- A finite disjoint union of schemes in a chosen big pro-étale site lies in it. -/
theorem contains_sigma {ι : Type} [Finite ι] (Y : ι → Scheme.{u})
    (hY : ∀ i, B.Contains (Y i)) : B.Contains (∐ Y) := by
  show (∐ Y).size < B.cutoff
  rw [← Scheme.size_congr (Sigma.reindex (Equiv.ulift : ULift.{u} ι ≃ ι) Y)]
  exact Scheme.size_sigmaObj_lt B.aleph0_lt_cutoff B.aleph0_lt_cutoff_cof
    Cardinal.mk_le_aleph0 _ (fun i ↦ hY i.down)

/-- The disjoint union of a finite family of objects of the small pro-étale site, built from the
disjoint union of their underlying schemes. -/
def sigmaCofan {ι : Type} [Finite ι] (X : ι → SmallProetale B S hS) : Cofan X := by
  let Y := fun i ↦ (toScheme B S hS).obj (X i)
  let Z : B.Scheme := ⟨∐ Y, contains_sigma B Y (fun i ↦ (X i).obj.left.property)⟩
  let g : Z ⟶ ⟨S, hS⟩ :=
    ObjectProperty.homMk (Limits.Sigma.desc fun i ↦ B.inclusion.map (X i).obj.hom)
  have hg : WeaklyEtale (B.inclusion.map g) :=
    IsZariskiLocalAtSource.sigmaDesc (fun i ↦ (X i).property)
  refine Cofan.mk ⟨Over.mk g, hg⟩ (fun i ↦ ObjectProperty.homMk (Over.homMk
    (ObjectProperty.homMk (Sigma.ι Y i)) ?_))
  apply B.inclusion.map_injective
  change Sigma.ι Y i ≫ Limits.Sigma.desc _ = _
  simp

/-- The underlying scheme of `sigmaCofan` is the disjoint union of the underlying schemes. -/
def isColimitMapCoconeSigmaCofan {ι : Type} [Finite ι] (X : ι → SmallProetale B S hS) :
    IsColimit ((toScheme B S hS).mapCocone (sigmaCofan B S hS X)) :=
  (isColimitMapCoconeCofanMkEquiv (toScheme B S hS) X _).symm (coproductIsCoproduct _)

/-- `sigmaCofan` is a coproduct in the small pro-étale site. -/
def isColimitSigmaCofan {ι : Type} [Finite ι] (X : ι → SmallProetale B S hS) :
    IsColimit (sigmaCofan B S hS X) := by
  let H := toScheme B S hS
  refine Cofan.IsColimit.mk _ (fun s ↦ ObjectProperty.homMk (Over.homMk
    (ObjectProperty.homMk (Limits.Sigma.desc (fun i ↦ H.map (s.inj i)))) ?_)) ?_ ?_
  · apply B.inclusion.map_injective
    change Limits.Sigma.desc _ ≫ B.inclusion.map s.pt.obj.hom = Limits.Sigma.desc _
    refine Sigma.hom_ext _ _ fun i ↦ ?_
    simp only [Sigma.ι_desc_assoc, Sigma.ι_desc]
    change B.inclusion.map (s.inj i).hom.left ≫ B.inclusion.map s.pt.obj.hom = _
    rw [← Functor.map_comp, Over.w]
  · intro s i
    apply H.map_injective
    change Sigma.ι _ i ≫ Limits.Sigma.desc _ = _
    simp
  · intro s m hm
    apply H.map_injective
    refine Sigma.hom_ext _ _ fun i ↦ ?_
    have hi := congrArg H.map (hm i)
    change Sigma.ι _ i ≫ H.map m = H.map (s.inj i) at hi
    change Sigma.ι (fun i ↦ H.obj (X i)) i ≫ H.map m =
      Sigma.ι (fun i ↦ H.obj (X i)) i ≫ Limits.Sigma.desc (fun i ↦ H.map (s.inj i))
    simpa only [Sigma.ι_desc] using hi

/-- The small pro-étale site has finite coproducts. -/
instance hasFiniteCoproducts : HasFiniteCoproducts (SmallProetale B S hS) := by
  have H (ι : Type) [Finite ι] : HasColimitsOfShape (Discrete ι) (SmallProetale B S hS) :=
    { has_colimit := fun F ↦ ⟨⟨
        (Cocone.precompose Discrete.natIsoFunctor.hom).obj
          (sigmaCofan B S hS (fun j ↦ F.obj ⟨j⟩)),
        (IsColimit.precomposeHomEquiv _ _).symm (isColimitSigmaCofan B S hS _)⟩⟩ }
  exact ⟨fun n ↦ H (Fin n)⟩

/-- Finite coproducts in the small pro-étale site are computed on underlying schemes. -/
instance toScheme_preservesFiniteCoproducts : PreservesFiniteCoproducts (toScheme B S hS) := by
  refine ⟨fun n ↦ ?_⟩
  have (X : Fin n → SmallProetale B S hS) :
      PreservesColimit (Discrete.functor X) (toScheme B S hS) :=
    preservesColimit_of_preserves_colimit_cocone (isColimitSigmaCofan B S hS X)
      (isColimitMapCoconeSigmaCofan B S hS X)
  exact preservesColimitsOfShape_of_discrete _

/-- Coproducts of finite families in any universe are computed on underlying schemes. -/
instance toScheme_preservesColimitsOfShape_discrete (ι : Type w) [Finite ι] :
    PreservesColimitsOfShape (Discrete ι) (toScheme B S hS) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  exact preservesColimitsOfShape_of_equiv (Discrete.equivalence e.symm) _

/-- The small pro-étale site is finitary extensive: its finite coproducts are disjoint and
universal, as they are in schemes. -/
instance finitaryExtensive : FinitaryExtensive (SmallProetale B S hS) :=
  finitaryExtensive_of_preserves_and_reflects_isomorphism (toScheme B S hS)

/-- The summands of a finite disjoint union in the small pro-étale site cover it. -/
theorem ofArrows_mem_topology_of_isColimit {ι : Type w} [Finite ι]
    {Y : ι → SmallProetale B S hS} (c : Cofan Y) (hc : IsColimit c) :
    Sieve.ofArrows Y c.inj ∈ topology B S hS c.pt := by
  refine Precoverage.generate_mem_toGrothendieck
    (SmallProetale.mem_precoverage_of_map_mem B ⟨S, hS⟩ ?_)
  rw [Presieve.map_ofArrows]
  exact zariskiPrecoverage_le_proetalePrecoverage _ <|
    Scheme.ofArrows_mem_zariskiPrecoverage_of_isColimit _
      ((Cofan.isColimitMapCoconeEquiv (toScheme B S hS) Y c) (isColimitOfPreserves _ hc))

end SmallProetale

end ProEtale

end AlgebraicGeometry
