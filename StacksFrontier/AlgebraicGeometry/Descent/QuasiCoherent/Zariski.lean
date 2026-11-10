module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.StackReduction
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentLocal

/-!
# Zariski descent for quasi-coherent modules

Stacks 023E asserts that for an open covering `S = ⋃ Uᵢ` every quasi-coherent descent datum for
the family `{Uᵢ ⟶ S}` is effective, and that the canonical descent functor of Stacks 023D is
fully faithful.  Its proof appeals to the gluing of sheaves of Sheaves, Section 00AK, and to the
locality of quasi-coherence of Modules, Definition 01BE.  This file supplies the Zariski
counterpart of
`StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherent/StackReduction.lean`: everything that part
of the argument gives *without* gluing, and the exact reduction of what is left.

## Main definitions

There are no new definitions.

## Main results

* `Stacks.Descent.hom_ext_of_restrictFunctor_map_eq` and
  `Stacks.Descent.hom_ext_of_pullback_map_eq`: a morphism of sheaves of modules on a scheme is
  determined by its restrictions, equivalently by its pullbacks, along a family of open
  immersions whose images cover the scheme.  This is the separatedness half of the gluing of
  Sheaves, Section 00AK.
* `Stacks.Descent.epi_of_restrictFunctor_map_epi`, `Stacks.Descent.epi_of_pullback_map_epi` and
  `Stacks.Descent.epi_of_restrictFunctor_map_epi_opens`: **being an epimorphism is local on the
  scheme**.  A morphism of sheaves of modules whose restriction, equivalently pullback, along
  each member of such a family is an epimorphism is an epimorphism.
* `Stacks.Descent.faithful_toDescentData_of_iSup_opensRange_eq_top`: for such a family the
  functor `CategoryTheory.Pseudofunctor.toDescentData` of
  `AlgebraicGeometry.modulePullbackPseudofunctor` is faithful.
* `Stacks.Descent.faithful_canonicalDescentFunctor_zariski` and
  `Stacks.Descent.faithful_canonicalDescentFunctor_openCover`: the **faithfulness** half of
  Stacks 023E, for a jointly surjective family of open immersions and for an
  `AlgebraicGeometry.Scheme.OpenCover` respectively.
* `Stacks.Descent.isQuasicoherent_of_restrictFunctor_zariski` and
  `Stacks.Descent.isQuasicoherent_of_pullback_zariski`: quasi-coherence descends along such a
  family.  This discharges the standing hypothesis of
  `Stacks.Descent.isEffective_of_essImage` and `Stacks.Descent.isEffective_of_essSurj`, so that
  `Stacks.Descent.isEffective_of_essSurj_zariski` and
  `Stacks.Descent.isEffective_of_essSurj_openCover` deduce the effectivity half of Stacks 023E
  from the gluing of *arbitrary* sheaves of modules, with no quasi-coherence side condition.
* `Stacks.Descent.nonempty_fullyFaithful_canonicalDescentFunctor_of_isPrestack_of_sieve_mem` and
  `Stacks.Descent.isEffective_of_isStack_of_sieve_mem`: the two halves of Stacks 023T for an
  arbitrary Grothendieck topology on schemes.  These generalise
  `Stacks.Descent.nonempty_fullyFaithful_canonicalDescentFunctor_of_isPrestack` and
  `Stacks.Descent.isEffective_of_isStack`, which are their fpqc instances, and
  `Stacks.Descent.nonempty_fullyFaithful_canonicalDescentFunctor_openCover_of_isPrestack` and
  `Stacks.Descent.isEffective_openCover_of_isStack` are their Zariski ones.

## What Stacks 023E still needs

The two statements of Stacks 023E are *not* proved here, because the gluing half of Sheaves,
Section 00AK is missing from the library for sheaves of modules on a scheme.  Precisely, for a
family `f i : X i ⟶ S` of open immersions with `⨆ i, (f i).opensRange = ⊤`, what remains is:

* `(AlgebraicGeometry.modulePullbackPseudofunctor.toDescentData f).Full`, equivalently the
  gluing of morphisms: a family of morphisms `M|_{X i} ⟶ N|_{X i}` compatible over the overlaps
  comes from a morphism `M ⟶ N`.  With
  `Stacks.Descent.faithful_toDescentData_of_iSup_opensRange_eq_top` this gives
  `Nonempty (AlgebraicGeometry.canonicalDescentFunctor f).FullyFaithful` through
  `Stacks.Descent.nonempty_fullyFaithful_canonicalDescentFunctor_of_fullyFaithful`.
* `(AlgebraicGeometry.modulePullbackPseudofunctor.toDescentData f).EssSurj`, equivalently the
  gluing of sheaves of modules.  By
  `Stacks.Descent.isEffective_of_essSurj_zariski` this gives the effectivity half outright.

The two gluing statements exist in the library in neighbouring presentations, which is where a
proof should start: `internalHom_glue` and `internalHom_isSheaf` (the latter tagged
`@[stacks 03EM]`), both in
`StacksFrontier/Algebra/Category/ModuleCat/Presheaf/InternalHom.lean`, prove the gluing of morphisms
of presheaves of modules on an arbitrary ringed site, with restriction taken as the slice-site
pushforward rather than `AlgebraicGeometry.Scheme.Modules.restrictFunctor`;
`TopCat.Sheaf.existsUnique_hom_of_localHom`
(`StacksFrontier/Topology/Sheaves/Glueing/MapGluing.lean`, tagged `@[stacks 04TN]`) proves it for
sheaves of types on a space in exactly the `⨆ i, U i = ⊤` shape used here; and
`StacksFrontier/Topology/Sheaves/Glueing/Sheaf.lean` and
`StacksFrontier/Topology/Sheaves/Glueing/AlgebraicStructure.lean` (Stacks 00AL and 00AM) glue
sheaves
of types, of abelian groups and of modules over a *fixed* ring from cover data, but not modules over
a structure sheaf.

## Implementation notes

The separatedness statement is proved on sections.  A morphism of sheaves of modules on a scheme
is determined by its maps on sections (`AlgebraicGeometry.Scheme.Modules.hom_ext`), the open `U`
is covered by the opens `(f i).opensRange ⊓ U`, and the restriction of a section of the target to
one of those opens is computed by naturality.  What makes the step from the hypothesis to the
individual open free is that `AlgebraicGeometry.Scheme.Modules.restrictFunctor` is a pushforward
along `AlgebraicGeometry.Scheme.Hom.opensFunctor`, so
`((restrictFunctor f).map φ).app W` is *definitionally* `φ.app (f ''ᵁ W)`; taking `W` to be
`f ⁻¹ᵁ U` and rewriting with
`AlgebraicGeometry.Scheme.Hom.image_preimage_eq_opensRange_inf` lands exactly on the open of the
cover.  The `AlgebraicGeometry.Scheme.Modules.pullback` form is obtained from the `restrictFunctor`
form through `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`, at the level of
natural transformations rather than components.

Locality of being an epimorphism is a formal consequence of that separatedness, and of nothing
else.  `CategoryTheory.Epi` is a cancellation property, so a pair of morphisms out of the target
equalised by `φ` is equalised by every restriction of `φ`, each of which cancels it; the
separatedness statement then identifies the two morphisms themselves.  In particular no local
surjectivity criterion for sheaves of modules — an identification of `CategoryTheory.Epi` with
`CategoryTheory.Sheaf.IsLocallySurjective` — is needed, and neither is exactness of the
restriction functor.

Descent of quasi-coherence is obtained from `Stacks.Modules.isQuasicoherent_of_restrict`, which
is stated for a family of *opens* covering the scheme.  Passing from an arbitrary open immersion
`g` to its open image costs one isomorphism: `AlgebraicGeometry.Scheme.Hom.isoOpensRange_inv_comp`
makes `g.opensRange.ι` a composite `g.isoOpensRange.inv ≫ g`, so
`AlgebraicGeometry.Scheme.Modules.restrictFunctorComp` identifies the restriction to the image
with a further restriction of the restriction along `g`, and quasi-coherence of the latter is
`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_restrictFunctor`.

The reductions of Stacks 023T are stated for a variable Grothendieck topology rather than for
the fpqc one; the proofs are those of `StackReduction.lean` with the topology left free, and the
fpqc statements there are the instances at `AlgebraicGeometry.Scheme.fpqcTopology`.

## References

* [Stacks Project, Tag 00AK](https://stacks.math.columbia.edu/tag/00AK)
* [Stacks Project, Tag 023D](https://stacks.math.columbia.edu/tag/023D)
* [Stacks Project, Tag 023E](https://stacks.math.columbia.edu/tag/023E)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Bicategory Opposite TopologicalSpace

universe v u

namespace Stacks.Descent

section Separated

variable {S : Scheme.{u}} {M N : S.Modules}

/-- Restricting a section of the target along an inclusion of opens commutes with a morphism of
sheaves of modules. -/
theorem presheaf_map_app_apply (φ : M ⟶ N) {U V : S.Opens} (i : V ⟶ U) (x : Γ(M, U)) :
    N.presheaf.map i.op (φ.app U x) = φ.app V (M.presheaf.map i.op x) :=
  (NatTrans.naturality_apply φ.mapPresheaf i.op x).symm

/-- **Separatedness of morphisms of sheaves of modules for the Zariski topology.**  A morphism of
sheaves of modules on a scheme is determined by its restrictions along a family of open immersions
whose images cover the scheme.

This is the separatedness half of the gluing of Sheaves, Section 00AK, which is what Stacks 023E
appeals to. -/
theorem hom_ext_of_restrictFunctor_map_eq {I : Type v} {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ S)
    [∀ i, IsOpenImmersion (f i)] (hf : ⨆ i, (f i).opensRange = ⊤) {φ ψ : M ⟶ N}
    (h : ∀ i, (Scheme.Modules.restrictFunctor (f i)).map φ =
      (Scheme.Modules.restrictFunctor (f i)).map ψ) :
    φ = ψ := by
  ext U x
  have hcover : U ≤ ⨆ i, ((f i).opensRange ⊓ U) := by
    simp only [← iSup_inf_eq, hf, top_inf_eq, le_refl]
  refine TopCat.Sheaf.eq_of_locally_eq' (⟨N.presheaf, N.isSheaf⟩ : TopCat.Sheaf Ab.{u} S)
    (fun i ↦ (f i).opensRange ⊓ U) U (fun i ↦ homOfLE inf_le_right) hcover _ _ fun i ↦ ?_
  have h' : φ.app (f i ''ᵁ (f i ⁻¹ᵁ U)) = ψ.app (f i ''ᵁ (f i ⁻¹ᵁ U)) :=
    congrArg (fun θ ↦ Scheme.Modules.Hom.app θ (f i ⁻¹ᵁ U)) (h i)
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf] at h'
  rw [presheaf_map_app_apply φ (homOfLE inf_le_right) x,
    presheaf_map_app_apply ψ (homOfLE inf_le_right) x, h']

/-- **Separatedness of morphisms of sheaves of modules for the Zariski topology**, in terms of
pullback rather than restriction.  A morphism of sheaves of modules on a scheme is determined by
its pullbacks along a family of open immersions whose images cover the scheme. -/
theorem hom_ext_of_pullback_map_eq {I : Type v} {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ S)
    [∀ i, IsOpenImmersion (f i)] (hf : ⨆ i, (f i).opensRange = ⊤) {φ ψ : M ⟶ N}
    (h : ∀ i, (Scheme.Modules.pullback (f i)).map φ = (Scheme.Modules.pullback (f i)).map ψ) :
    φ = ψ := by
  refine hom_ext_of_restrictFunctor_map_eq f hf fun i ↦ ?_
  have key : ∀ θ : M ⟶ N, (Scheme.Modules.restrictFunctor (f i)).map θ =
      (Scheme.Modules.restrictFunctorIsoPullback (f i)).hom.app M ≫
        (Scheme.Modules.pullback (f i)).map θ ≫
          (Scheme.Modules.restrictFunctorIsoPullback (f i)).inv.app N := fun θ ↦ by
    rw [← NatTrans.naturality_assoc]
    simp
  rw [key φ, key ψ, h i]

/-- If morphisms out of `N` are detected by the functors `F i`, then `φ` is an epimorphism as soon
as every `F i` sends it to an epimorphism. -/
private theorem epi_of_forall_map_epi {I : Type v} {D : I → Type*} [∀ i, Category (D i)]
    (F : ∀ i, S.Modules ⥤ D i) (φ : M ⟶ N)
    (hext : ∀ {Q : S.Modules} {u v : N ⟶ Q}, (∀ i, (F i).map u = (F i).map v) → u = v)
    (h : ∀ i, Epi ((F i).map φ)) : Epi φ :=
  ⟨fun {_} _ _ huv ↦ hext fun i ↦ (cancel_epi ((F i).map φ)).mp <| by
    rw [← Functor.map_comp, ← Functor.map_comp, huv]⟩

/-- **Being an epimorphism is local on a scheme for morphisms of sheaves of modules.**  If the
restriction of `φ : M ⟶ N` along each member of a family of open immersions whose images cover
the scheme is an epimorphism, then `φ` is an epimorphism.

Surjectivity of a morphism of sheaves of modules is phrased categorically, as
`CategoryTheory.Epi`, and in that phrasing locality is formal: a pair of morphisms out of `N`
equalised by `φ` is equalised by each restriction of `φ`, hence the two restrictions agree by
`Stacks.Descent.hom_ext_of_restrictFunctor_map_eq`, hence the two morphisms agree.  No
sheafification, no local surjectivity criterion and no exactness of the restriction functor is
involved. -/
theorem epi_of_restrictFunctor_map_epi {I : Type v} {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ S)
    [∀ i, IsOpenImmersion (f i)] (hf : ⨆ i, (f i).opensRange = ⊤) (φ : M ⟶ N)
    (h : ∀ i, Epi ((Scheme.Modules.restrictFunctor (f i)).map φ)) : Epi φ := by
  exact epi_of_forall_map_epi (fun i ↦ Scheme.Modules.restrictFunctor (f i)) φ
    (hom_ext_of_restrictFunctor_map_eq f hf) h

/-- **Being an epimorphism is local on a scheme**, in terms of pullback rather than restriction.
If the pullback of `φ : M ⟶ N` along each member of a family of open immersions whose images
cover the scheme is an epimorphism, then `φ` is an epimorphism. -/
theorem epi_of_pullback_map_epi {I : Type v} {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ S)
    [∀ i, IsOpenImmersion (f i)] (hf : ⨆ i, (f i).opensRange = ⊤) (φ : M ⟶ N)
    (h : ∀ i, Epi ((Scheme.Modules.pullback (f i)).map φ)) : Epi φ := by
  exact epi_of_forall_map_epi (fun i ↦ Scheme.Modules.pullback (f i)) φ
    (hom_ext_of_pullback_map_eq f hf) h

/-- **Being an epimorphism is local on a scheme**, for a covering family of open subschemes.
This is `Stacks.Descent.epi_of_restrictFunctor_map_epi` for the inclusions of a family of opens
covering the scheme, which is the shape a cover of a test scheme is usually presented in. -/
theorem epi_of_restrictFunctor_map_epi_opens {I : Type u} {U : I → S.Opens}
    (hU : ⨆ i, U i = ⊤) (φ : M ⟶ N)
    (h : ∀ i, Epi ((Scheme.Modules.restrictFunctor (U i).ι).map φ)) : Epi φ :=
  epi_of_restrictFunctor_map_epi (fun i ↦ (U i).ι)
    (by simpa only [Scheme.Opens.opensRange_ι] using hU) φ h

end Separated

section Faithful

variable {S : Scheme.{u}} {I : Type v} {X : I → Scheme.{u}}

/-- Every member of a family of morphisms belonging to the Zariski precoverage is an open
immersion. -/
theorem isOpenImmersion_of_mem_zariskiPrecoverage {f : ∀ i, X i ⟶ S}
    (hf : Presieve.ofArrows X f ∈ Scheme.zariskiPrecoverage.{u} S) (i : I) :
    IsOpenImmersion (f i) :=
  ((Scheme.ofArrows_mem_precoverage_iff _).1 hf).2 i

/-- The images of a family of morphisms belonging to the Zariski precoverage cover the target.
This is the lattice form of the joint surjectivity half of the membership. -/
theorem iSup_opensRange_eq_top_of_mem_zariskiPrecoverage {f : ∀ i, X i ⟶ S}
    [∀ i, IsOpenImmersion (f i)]
    (hf : Presieve.ofArrows X f ∈ Scheme.zariskiPrecoverage.{u} S) :
    ⨆ i, (f i).opensRange = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨i, hi⟩ := ((Scheme.ofArrows_mem_precoverage_iff _).1 hf).1 x
  exact Opens.mem_iSup.2 ⟨i, hi⟩

/-- **Faithfulness of the descent functor for a Zariski covering family.**  For a family of open
immersions whose images cover the target, the canonical descent functor of
`AlgebraicGeometry.modulePullbackPseudofunctor` on all sheaves of modules is faithful. -/
theorem faithful_toDescentData_of_iSup_opensRange_eq_top (f : ∀ i, X i ⟶ S)
    [∀ i, IsOpenImmersion (f i)] (hf : ⨆ i, (f i).opensRange = ⊤) :
    (modulePullbackPseudofunctor.toDescentData f).Faithful where
  map_injective {_M _N _φ _ψ} h :=
    hom_ext_of_pullback_map_eq f hf fun i ↦ congrArg (fun θ ↦ θ.hom i) h

/-- **The faithfulness half of Stacks 023E.**  For a family of open immersions whose images cover
the target, the canonical descent functor of Stacks 023D on quasi-coherent modules is faithful.

This is the separated half of the full faithfulness asserted by Stacks 023E; the surjective half
is the gluing of morphisms, which is not proved here. -/
theorem faithful_canonicalDescentFunctor_zariski (f : ∀ i, X i ⟶ S)
    [∀ i, IsOpenImmersion (f i)] (hf : ⨆ i, (f i).opensRange = ⊤) :
    (canonicalDescentFunctor f).Faithful where
  map_injective {_M _N φ ψ} h := by
    apply ObjectProperty.hom_ext
    refine hom_ext_of_pullback_map_eq f hf fun i ↦ ?_
    exact (canonicalDescentFunctor_map_hom_hom f φ i).symm.trans
      ((congrArg (fun θ ↦ θ.hom.hom i) h).trans (canonicalDescentFunctor_map_hom_hom f ψ i))

/-- **The faithfulness half of Stacks 023E**, for an open covering of a scheme in the form of an
`AlgebraicGeometry.Scheme.OpenCover`. -/
theorem faithful_canonicalDescentFunctor_openCover (𝒰 : Scheme.OpenCover.{v} S) :
    (canonicalDescentFunctor 𝒰.f).Faithful :=
  faithful_canonicalDescentFunctor_zariski 𝒰.f 𝒰.iSup_opensRange

end Faithful

section Quasicoherent

variable {S : Scheme.{u}} {I : Type v} {X : I → Scheme.{u}}

/-- Quasi-coherence of the restriction of a module along an open immersion is quasi-coherence of
its restriction to the open image. -/
theorem isQuasicoherent_restrict_opensRange_ι {Z : Scheme.{u}} (g : Z ⟶ S) [IsOpenImmersion g]
    (M : S.Modules) (h : ((Scheme.Modules.restrictFunctor g).obj M).IsQuasicoherent) :
    ((Scheme.Modules.restrictFunctor g.opensRange.ι).obj M).IsQuasicoherent := by
  have := h
  exact isQuasicoherent_of_iso
    (((Scheme.Modules.restrictFunctorCongr g.isoOpensRange_inv_comp).symm ≪≫
      Scheme.Modules.restrictFunctorComp g.isoOpensRange.inv g).app M).symm
    (show ((Scheme.Modules.restrictFunctor g.isoOpensRange.inv).obj
      ((Scheme.Modules.restrictFunctor g).obj M)).IsQuasicoherent from inferInstance)

/-- **Descent of quasi-coherence along a Zariski covering family.**  A sheaf of modules on a
scheme whose restriction along each member of a family of open immersions with covering images is
quasi-coherent is itself quasi-coherent.

This is Stacks 01BE's locality of quasi-coherence, in the form in which an arbitrary covering
family rather than a family of opens presents it. -/
theorem isQuasicoherent_of_restrictFunctor_zariski (f : ∀ i, X i ⟶ S)
    [∀ i, IsOpenImmersion (f i)] (hf : ⨆ i, (f i).opensRange = ⊤) (M : S.Modules)
    (h : ∀ i, ((Scheme.Modules.restrictFunctor (f i)).obj M).IsQuasicoherent) :
    M.IsQuasicoherent :=
  Stacks.Modules.isQuasicoherent_of_restrict M (fun i ↦ (f i).opensRange) hf
    fun i ↦ isQuasicoherent_restrict_opensRange_ι (f i) M (h i)

/-- **Descent of quasi-coherence along a Zariski covering family**, in terms of pullback rather
than restriction.  This is the hypothesis of `Stacks.Descent.isEffective_of_essImage` and
`Stacks.Descent.isEffective_of_essSurj`, discharged for a Zariski covering family. -/
theorem isQuasicoherent_of_pullback_zariski (f : ∀ i, X i ⟶ S)
    [∀ i, IsOpenImmersion (f i)] (hf : ⨆ i, (f i).opensRange = ⊤) (M : S.Modules)
    (h : ∀ i, ((Scheme.Modules.pullback (f i)).obj M).IsQuasicoherent) :
    M.IsQuasicoherent :=
  isQuasicoherent_of_restrictFunctor_zariski f hf M fun i ↦
    isQuasicoherent_of_iso ((Scheme.Modules.restrictFunctorIsoPullback (f i)).app M).symm (h i)

/-- **The effectivity half of Stacks 023E, reduced to the gluing of arbitrary sheaves of
modules.**  For a family of open immersions whose images cover the target, essential surjectivity
of `CategoryTheory.Pseudofunctor.toDescentData` of
`AlgebraicGeometry.modulePullbackPseudofunctor` — which is about *all* sheaves of modules — already
gives effectivity of every quasi-coherent descent datum, with no further hypothesis: the module
produced on the base is quasi-coherent by
`Stacks.Descent.isQuasicoherent_of_pullback_zariski`. -/
theorem isEffective_of_essSurj_zariski (f : ∀ i, X i ⟶ S) [∀ i, IsOpenImmersion (f i)]
    (hf : ⨆ i, (f i).opensRange = ⊤)
    [(modulePullbackPseudofunctor.toDescentData f).EssSurj]
    (D : QuasicoherentDescentData f) : D.IsEffective :=
  isEffective_of_essSurj (isQuasicoherent_of_pullback_zariski f hf) D

/-- **The effectivity half of Stacks 023E, reduced to the gluing of arbitrary sheaves of
modules**, for an open covering of a scheme in the form of an
`AlgebraicGeometry.Scheme.OpenCover`. -/
theorem isEffective_of_essSurj_openCover (𝒰 : Scheme.OpenCover.{v} S)
    [(modulePullbackPseudofunctor.toDescentData 𝒰.f).EssSurj]
    (D : QuasicoherentDescentData 𝒰.f) : D.IsEffective :=
  isEffective_of_essSurj_zariski 𝒰.f 𝒰.iSup_opensRange D

end Quasicoherent

section Reduction

variable {I : Type v} {S : Scheme.{u}} {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ S}
  {J : GrothendieckTopology Scheme.{u}}

/-- **The full faithfulness half of Stacks 023D's descent functor, reduced to a prestack
condition for an arbitrary topology.**  If the pseudofunctor of quasi-coherent modules is a
prestack for a Grothendieck topology `J` and the family `f` generates a `J`-covering sieve, then
the canonical descent functor on quasi-coherent modules is fully faithful.

`Stacks.Descent.nonempty_fullyFaithful_canonicalDescentFunctor_of_isPrestack` is the case of the
fpqc topology; the Zariski case is
`Stacks.Descent.nonempty_fullyFaithful_canonicalDescentFunctor_openCover_of_isPrestack`. -/
theorem nonempty_fullyFaithful_canonicalDescentFunctor_of_isPrestack_of_sieve_mem
    [qcohPseudofunctor.IsPrestack J] (hf : Sieve.ofArrows X f ∈ J S) :
    Nonempty (canonicalDescentFunctor f).FullyFaithful := by
  have hb := (Functor.FullyFaithful.nonempty_iff_map_bijective
    (qcohPseudofunctor.toDescentData f)).1
      ⟨qcohPseudofunctor.fullyFaithfulToDescentData f hf⟩
  refine (Functor.FullyFaithful.nonempty_iff_map_bijective _).2 fun M N ↦ ?_
  have hcomp : ((canonicalDescentFunctor f).map : (M ⟶ N) → _) =
      homForget ∘ ((qcohPseudofunctor.toDescentData f).map : (M ⟶ N) → _) :=
    funext fun φ ↦ canonicalDescentFunctor_map_eq φ
  rw [hcomp]
  exact homForget_bijective.comp (hb M N)

/-- **The effectivity half of Stacks 023D's descent functor, reduced to a stack condition for an
arbitrary topology.**  If the pseudofunctor of quasi-coherent modules is a stack for a
Grothendieck topology `J` and the family `f` generates a `J`-covering sieve, then every
quasi-coherent descent datum for `f` is effective.

`Stacks.Descent.isEffective_of_isStack` is the case of the fpqc topology; the Zariski case is
`Stacks.Descent.isEffective_openCover_of_isStack`.  Unlike
`Stacks.Descent.isEffective_of_essSurj` there is no hypothesis that quasi-coherence descends
along `f`, because quasi-coherence is part of the objects of
`Stacks.Descent.qcohPseudofunctor`. -/
theorem isEffective_of_isStack_of_sieve_mem [qcohPseudofunctor.IsStack J]
    (hf : Sieve.ofArrows X f ∈ J S) (D : QuasicoherentDescentData f) : D.IsEffective := by
  have := qcohPseudofunctor.isEquivalence_toDescentData f hf
  obtain ⟨M, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage
    (F := qcohPseudofunctor.toDescentData f) (descentDataLift D)
  exact ⟨M, ⟨eqToIso (descentDataForgetFunctor_obj_toDescentData M).symm ≪≫
    descentDataForgetFunctor.mapIso e ≪≫
      eqToIso (descentDataForgetFunctor_obj_descentDataLift D)⟩⟩

/-- **The full faithfulness half of Stacks 023E, reduced to the Zariski prestack condition.** -/
theorem nonempty_fullyFaithful_canonicalDescentFunctor_openCover_of_isPrestack
    [qcohPseudofunctor.IsPrestack Scheme.zariskiTopology.{u}] (𝒰 : Scheme.OpenCover.{v} S) :
    Nonempty (canonicalDescentFunctor 𝒰.f).FullyFaithful :=
  nonempty_fullyFaithful_canonicalDescentFunctor_of_isPrestack_of_sieve_mem
    𝒰.mem_grothendieckTopology

/-- **The effectivity half of Stacks 023E, reduced to the Zariski stack condition.** -/
theorem isEffective_openCover_of_isStack
    [qcohPseudofunctor.IsStack Scheme.zariskiTopology.{u}] (𝒰 : Scheme.OpenCover.{v} S)
    (D : QuasicoherentDescentData 𝒰.f) : D.IsEffective :=
  isEffective_of_isStack_of_sieve_mem 𝒰.mem_grothendieckTopology D

end Reduction

end Stacks.Descent

end

end
