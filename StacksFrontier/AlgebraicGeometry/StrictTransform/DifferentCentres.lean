module

public import StacksFrontier.AlgebraicGeometry.Blowup.IsoOffCentre
public import StacksFrontier.AlgebraicGeometry.StrictTransform.Iterated

/-!
# Strict transforms for two centres differing by an effective Cartier divisor

Let `S` be a scheme, let `I` be a quasi-coherent ideal sheaf on `S` and let `D` be an effective
Cartier divisor on `S`. [Stacks, Tag 080H] says that blowing up `S` in `I * D` gives the same
scheme over `S` as blowing up it in `I` — part (1) — and that for a morphism `f : X ⟶ S` and a
sheaf of `𝒪_X`-modules `F` with no nonzero local sections supported in `f^{-1}D`, the two strict
transforms of `F` agree under the induced identification of the two base changes — part (2).

**Part (2) is proved here**, taking the isomorphism of blowups of part (1) as the hypothesis `e`
the tag's own statement of part (2) uses. Part (1) is not in the repository; see the
implementation notes.

The content of part (2) is that enlarging the centre from `I` to `I * D` does not enlarge the
submodule of supported sections that is divided out: over the complement of the exceptional
preimage of the first blowup the projection `pr_X` of the base change is an open immersion
([Stacks, Tag 02OS] part (1), the instance
`AlgebraicGeometry.isIso_blowUpToBase_restrict_compl_support`), so there `pr_X^* F` is a
restriction of `F` along an open immersion and the hypothesis on `F` applies. The two quotient
maps out of `pr_X^* F` then have the same kernel.

## Main definitions

* `Stacks.StrictTransform.mulBaseChangeIso`: the identification of the base changes
  `X ×_S Bl_I S` and `X ×_S Bl_{I·D} S` induced by an isomorphism of the two blowups over `S`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.supportedSections_eq_zero_of_restrict_open`: a section over
  an open `U` vanishes as soon as the restriction of the module to `U` has no nonzero sections
  supported in the inverse image of the subset.
* `AlgebraicGeometry.Scheme.Modules.supportedSections_eq_zero_of_pullback_on_open`: having no
  nonzero sections supported in a subset is inherited by the pullback along a morphism, on an
  open over which that morphism is an open immersion.
* `Stacks.StrictTransform.exists_sheaf_iso_of_preimage_exceptionalPreimage_union`: the
  comparison of the two strict transforms, for an arbitrary pair of morphisms whose base changes
  are identified compatibly with the projection to `X` and whose exceptional preimages differ by
  a subset in which the pullback of `F` has no nonzero sections away from the first exceptional
  preimage. No blowups occur in it.
* `Stacks.StrictTransform.supportedSections_pullback_fst_eq_zero`: that last condition for a
  blowup and `D`, from the hypothesis of the tag on `F`.
* `Stacks.StrictTransform.exists_baseChange_iso_sheaf_iso_mul`: **[Stacks, Tag 080H] part (2)**,
  in the shape the tag states it — the identification of the two base changes, its two
  projection formulas, and the isomorphism of strict transforms.

## Implementation notes

**Part (1) of the tag is not in the repository**, which is why
`Stacks.StrictTransform.exists_baseChange_iso_sheaf_iso_mul` takes the isomorphism `e` of the two
blowups over `S` as a hypothesis: that is exactly how the source states part (2), whose statement
is about the identification part (1) provides. Part (1) is the composite of [Stacks, Tag 080A]
(blowing up `I` and then the inverse image of `D` is blowing up `I * D`) with [Stacks, Tag 0807]
(the blowup of an effective Cartier divisor is an isomorphism) applied to the inverse image of
`D` on the blowup of `I`, which is an effective Cartier divisor by [Stacks, Tag 0809]. Of those
three, only 0807 is in the repository —
`Stacks.Blowup.isIso_blowUpToBase_of_isEffectiveCartierDivisor`
(`StacksFrontier/AlgebraicGeometry/Blowup/CartierCentre.lean`) — and 080A needs two further
absent tags, 01WU and 07ZV, that a product of effective Cartier divisors is one and conversely
each factor is, plus 01WW, that the inverse image of a product of ideal sheaves is the product
of the inverse images. So part (1) is a chain of five absent tags rather than a single step.
Only `e` is missing here; everything else about part (2) is unconditional.

The general form
`Stacks.StrictTransform.exists_sheaf_iso_of_preimage_exceptionalPreimage_union` mentions no
blowup and no divisor: all it needs is the identification `g` of the two base changes over `X`,
the set identity for the exceptional preimages, and the vanishing of the supported sections of
`pr_X^* F` in the extra subset over opens disjoint from the first exceptional preimage. That is
the same division of labour as
`Stacks.StrictTransform.iso_preimage_exceptionalPreimage`, and it is what keeps the blowup
instance a three-line application. The comparison itself is
`Stacks.Abelian.isoOfEpiSameKernel` for the two quotient maps, read over the open
`g^{-1}(exceptionalComplement f b' E')` — written with the *open*
`Stacks.StrictTransform.exceptionalComplement` rather than as the complement of the closed
`Stacks.StrictTransform.exceptionalPreimage`, since a `compl_compl` rewrite under a binder does
not fire.

Both quotient maps become isomorphisms over that open and both targets have no sections
supported in its complement; for the strict transform in the smaller centre `I` that last fact
is *not* its defining property but
`AlgebraicGeometry.Scheme.Modules.supportedSectionsSubmodule_union_eq` applied to it, which is
where the hypothesis on `F` enters.

The statements are given for an arbitrary module `F`, with no quasi-coherence hypothesis, which
is more general than the tag: `Stacks.StrictTransform.sheaf` is a cokernel and needs none.

## References

* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 080D](https://stacks.math.columbia.edu/tag/080D)
* [Stacks Project, Tag 080H](https://stacks.math.columbia.edu/tag/080H)
* [Stacks Project, Tag 084L](https://stacks.math.columbia.edu/tag/084L)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- A section of `F` over an open `U` which is supported in a subset `Z` vanishes, as soon as the
restriction of `F` to `U` has no nonzero sections supported in the inverse image of `Z`. This is
the converse direction of
`AlgebraicGeometry.Scheme.Modules.supportedSections_eq_zero_of_restrict`, read at the top open of
`U`. -/
public theorem supportedSections_eq_zero_of_restrict_open (G : X.Modules) (Z : Set X)
    (U : X.Opens)
    (h : ∀ (U' : U.toScheme.Opens) (t : Γ(G.restrict U.ι, U')),
      t ∈ (supportedSectionsSubmodule (U.ι.base ⁻¹' Z)
        (G.restrict U.ι)).toSubmodule.obj (op U') → t = 0)
    (s : Γ(G, U)) (hs : s ∈ (supportedSectionsSubmodule Z G).toSubmodule.obj (op U)) :
    s = 0 := by
  have himg : U.ι ''ᵁ (⊤ : U.toScheme.Opens) = U := Scheme.Opens.ι_image_top U
  replace hs := (mem_supportedSectionsSubmodule_iff Z G U s).mp hs
  have hmem : G.presheaf.map (eqToHom himg).op s ∈
      (supportedSectionsSubmodule (U.ι.base ⁻¹' Z)
        (G.restrict U.ι)).toSubmodule.obj (op (⊤ : U.toScheme.Opens)) := by
    refine (mem_supportedSectionsSubmodule_iff (U.ι.base ⁻¹' Z) (G.restrict U.ι) ⊤ _).mpr ?_
    intro x hx hxZ
    have hxImg : U.ι.base x ∈ U.ι ''ᵁ (⊤ : U.toScheme.Opens) := ⟨x, trivial, rfl⟩
    have h0 := ConcreteCategory.congr_hom (germ_restrictStalkNatIso_hom_app U.ι x G hx)
      (G.presheaf.map (eqToHom himg).op s)
    have hRHS : (ConcreteCategory.hom (G.presheaf.germ
        (U.ι ''ᵁ (⊤ : U.toScheme.Opens)) (U.ι.base x) hxImg))
        (G.presheaf.map (eqToHom himg).op s) = 0 :=
      (TopCat.Presheaf.germ_res_apply G.presheaf (eqToHom himg) (U.ι.base x) hxImg s).trans
        (hs (U.ι.base x) x.2 hxZ)
    have hz : (ConcreteCategory.hom ((restrictStalkNatIso U.ι x).hom.app G))
        ((ConcreteCategory.hom ((G.restrict U.ι).presheaf.germ ⊤ x hx))
          (G.presheaf.map (eqToHom himg).op s)) = 0 :=
      (ConcreteCategory.comp_apply _ _ _).symm.trans (h0.trans hRHS)
    exact (ConcreteCategory.bijective_of_isIso
      ((restrictStalkNatIso U.ι x).hom.app G)).injective (hz.trans (map_zero _).symm)
  exact (ConcreteCategory.bijective_of_isIso (G.presheaf.map (eqToHom himg).op)).injective
    ((h ⊤ _ hmem).trans (map_zero _).symm)

/-- Over an open `U` on which `p` is an open immersion, the restriction of `p^* F` to `U` has no
nonzero sections supported in the inverse image of a subset in which `F` has none. -/
public theorem supportedSections_restrict_pullback_eq_zero {Y : Scheme.{u}} (p : X ⟶ Y)
    (Z : Set Y) (F : Y.Modules)
    (hF : ∀ (U : Y.Opens) (s : Γ(F, U)),
      s ∈ (supportedSectionsSubmodule Z F).toSubmodule.obj (op U) → s = 0)
    (U : X.Opens) [IsOpenImmersion (U.ι ≫ p)]
    (U' : U.toScheme.Opens) (t : Γ(((Scheme.Modules.pullback p).obj F).restrict U.ι, U'))
    (ht : t ∈ (supportedSectionsSubmodule (U.ι.base ⁻¹' (p.base ⁻¹' Z))
      (((Scheme.Modules.pullback p).obj F).restrict U.ι)).toSubmodule.obj (op U')) : t = 0 := by
  have hset : (U.ι ≫ p).base ⁻¹' Z = U.ι.base ⁻¹' (p.base ⁻¹' Z) := rfl
  have h0 := supportedSections_eq_zero_of_pullback (U.ι ≫ p) Z F hF
  rw [hset] at h0
  exact supportedSections_eq_zero_of_mono _
    (((restrictFunctorIsoPullback U.ι).app ((Scheme.Modules.pullback p).obj F)).hom ≫
      ((Scheme.Modules.pullbackComp U.ι p).app F).hom) inferInstance h0 U' t ht

/-- Having no nonzero sections supported in a subset is inherited by the pullback along a
morphism, over an open on which that morphism is an open immersion. Generalizes
`AlgebraicGeometry.Scheme.Modules.supportedSections_eq_zero_of_pullback`, which is the case
`U = ⊤`. -/
public theorem supportedSections_eq_zero_of_pullback_on_open {Y : Scheme.{u}} (p : X ⟶ Y)
    (Z : Set Y) (F : Y.Modules)
    (hF : ∀ (U : Y.Opens) (s : Γ(F, U)),
      s ∈ (supportedSectionsSubmodule Z F).toSubmodule.obj (op U) → s = 0)
    (U : X.Opens) [IsOpenImmersion (U.ι ≫ p)]
    (s : Γ((Scheme.Modules.pullback p).obj F, U))
    (hs : s ∈ (supportedSectionsSubmodule (p.base ⁻¹' Z)
      ((Scheme.Modules.pullback p).obj F)).toSubmodule.obj (op U)) : s = 0 :=
  supportedSections_eq_zero_of_restrict_open _ _ U
    (supportedSections_restrict_pullback_eq_zero p Z F hF U) s hs

end AlgebraicGeometry.Scheme.Modules

namespace Stacks.StrictTransform

open AlgebraicGeometry.Scheme.Modules hiding pullback

variable {X S S' S'' : Scheme.{u}}

/-- **The comparison of the two strict transforms.** Let `g` identify the base change of `f`
along `b` with the base change along `b'`, compatibly with the projections to `X`, and suppose
the inverse image under `g` of the exceptional preimage for `E'` is the exceptional preimage for
`E` together with a subset `ZD` in which `pr_X^* F` has no nonzero sections over opens disjoint
from the exceptional preimage for `E`. Then the strict transform along `b'` pulls back to the
strict transform along `b`.

Both quotient maps out of `pr_X^* F` become isomorphisms over the open complement of
`g^{-1}(pr_{S''}^{-1} Supp E')` and neither target has sections supported in its complement, so
they have the same kernel. For the strict transform along `b` the second of those facts is
`AlgebraicGeometry.Scheme.Modules.supportedSectionsSubmodule_union_eq`, which is where `hZD`
enters. This is the general form of [Stacks, Tag 080H] part (2); no blowup occurs in it. -/
public theorem exists_sheaf_iso_of_preimage_exceptionalPreimage_union (f : X ⟶ S) (b : S' ⟶ S)
    (b' : S'' ⟶ S) (E : S'.IdealSheafData) (E' : S''.IdealSheafData) (F : X.Modules)
    (ZD : Set (baseChange f b)) (g : baseChange f b ≅ baseChange f b')
    (hfst : g.hom ≫ pullback.fst f b' = pullback.fst f b)
    (hsupp : g.hom.base ⁻¹' exceptionalPreimage f b' E' = exceptionalPreimage f b E ∪ ZD)
    (hZD : ∀ (U : (baseChange f b).Opens),
      (U : Set (baseChange f b)) ∩ exceptionalPreimage f b E = ∅ →
      ∀ s : Γ((Scheme.Modules.pullback (pullback.fst f b)).obj F, U),
        s ∈ (supportedSectionsSubmodule ZD
          ((Scheme.Modules.pullback (pullback.fst f b)).obj F)).toSubmodule.obj (op U) → s = 0) :
    Nonempty ((Scheme.Modules.pullback g.hom).obj (sheaf f b' E' F) ≅ sheaf f b E F) := by
  set Z := exceptionalPreimage f b E with hZ
  set G := (Scheme.Modules.pullback (pullback.fst f b)).obj F with hG
  set V := g.hom ⁻¹ᵁ exceptionalComplement f b' E' with hV
  have hVcompl : ((V : Set (baseChange f b)))ᶜ = Z ∪ ZD := by
    rw [← hsupp, hV]
    ext x
    simp [exceptionalComplement, exceptionalPreimage]
  have hZclosed : IsClosed Z := E.support.isClosed.preimage (by fun_prop)
  have hN : supportedSectionsSubmodule (Z ∪ ZD) G = supportedSectionsSubmodule Z G :=
    supportedSectionsSubmodule_union_eq Z ZD hZclosed G hZD
  set α : (Scheme.Modules.pullback g.hom).obj
      ((Scheme.Modules.pullback (pullback.fst f b')).obj F) ≅ G :=
    (Scheme.Modules.pullbackComp g.hom (pullback.fst f b')).app F ≪≫
      (Scheme.Modules.pullbackCongr hfst).app F with hα
  set r := (Scheme.Modules.pullback g.hom).map (π f b' E' F) with hr
  set q := α.hom ≫ π f b E F with hq
  have hVle : V ≤ exceptionalComplement f b E := by
    intro x hx
    have hx' : x ∉ ((V : Set (baseChange f b)))ᶜ := by simpa using hx
    rw [hVcompl] at hx'
    exact fun hz => hx' (Or.inl hz)
  have : IsIso ((restrictFunctor (exceptionalComplement f b' E').ι).map (π f b' E' F)) :=
    isIso_restrictFunctor_map_π f b' E' F
  have : IsIso ((restrictFunctor V.ι).map r) :=
    isIso_restrictFunctor_map_pullback_map g.hom _ (π f b' E' F)
  have : IsIso ((restrictFunctor (exceptionalComplement f b E).ι).map (π f b E F)) :=
    isIso_restrictFunctor_map_π f b E F
  have : IsIso ((restrictFunctor V.ι).map (π f b E F)) :=
    isIso_restrictFunctor_map_of_le hVle _
  have : IsIso ((restrictFunctor V.ι).map q) := by
    rw [hq, Functor.map_comp]; infer_instance
  have : IsOpenImmersion g.hom := inferInstance
  have : Mono ((restrictAdjunction V.ι).unit.app
      ((Scheme.Modules.pullback g.hom).obj (sheaf f b' E' F))) := by
    refine mono_unit_app_of_supportedSections_eq_zero V _ ?_
    rw [hVcompl, ← hsupp]
    exact supportedSections_eq_zero_of_pullback g.hom (exceptionalPreimage f b' E') _
      (supportedSections_sheaf_eq_zero f b' E' F)
  have : Mono ((restrictAdjunction V.ι).unit.app (sheaf f b E F)) := by
    refine mono_unit_app_of_supportedSections_eq_zero V _ ?_
    rw [hVcompl]
    have hcok : cokernel (supportedSectionsι (Z ∪ ZD) G) = sheaf f b E F :=
      congrArg (fun N : G.Submodule => cokernel N.ι) hN
    have hc := supportedSections_cokernel_eq_zero_of_compl_eq V hVcompl.symm G
    rw [hcok] at hc
    exact hc
  have : Epi r := by rw [hr]; infer_instance
  have : Epi q := by rw [hq]; infer_instance
  refine ⟨Stacks.Abelian.isoOfEpiSameKernel r q (fun {A} a => ?_)⟩
  exact (comp_eq_zero_iff_restrictFunctor_map_eq_zero V r a).trans
    (comp_eq_zero_iff_restrictFunctor_map_eq_zero V q a).symm

/-- The identification of the base changes `X ×_S Bl_I S` and `X ×_S Bl_{I·D} S` induced by an
isomorphism `e` of the two blowups over `S`. It is the map of fibre products with `𝟙 X` on the
first factor and `e` on the second. -/
public noncomputable def mulBaseChangeIso (f : X ⟶ S) (I D : S.IdealSheafData)
    (e : Over.mk (AlgebraicGeometry.blowUpToBase I) ≅
      Over.mk (AlgebraicGeometry.blowUpToBase (I * D))) :
    baseChange f (AlgebraicGeometry.blowUpToBase I) ≅
      baseChange f (AlgebraicGeometry.blowUpToBase (I * D)) :=
  have : IsIso e.hom.left :=
    ⟨⟨e.inv.left, Over.hom_left_inv_left e, Over.inv_left_hom_left e⟩⟩
  asIso (pullback.map f (AlgebraicGeometry.blowUpToBase I) f
    (AlgebraicGeometry.blowUpToBase (I * D)) (𝟙 X) e.hom.left (𝟙 S)
    (by simp) (by simpa using (Over.w e.hom).symm))

/-- `Stacks.StrictTransform.mulBaseChangeIso` commutes with the projections to `X`. -/
public theorem mulBaseChangeIso_hom_fst (f : X ⟶ S) (I D : S.IdealSheafData)
    (e : Over.mk (AlgebraicGeometry.blowUpToBase I) ≅
      Over.mk (AlgebraicGeometry.blowUpToBase (I * D))) :
    (mulBaseChangeIso f I D e).hom ≫ pullback.fst f (AlgebraicGeometry.blowUpToBase (I * D)) =
      pullback.fst f (AlgebraicGeometry.blowUpToBase I) := by
  simp [mulBaseChangeIso, pullback.map]

/-- `Stacks.StrictTransform.mulBaseChangeIso` carries the projection to the second blowup to the
projection to the first followed by `e`. -/
public theorem mulBaseChangeIso_hom_snd (f : X ⟶ S) (I D : S.IdealSheafData)
    (e : Over.mk (AlgebraicGeometry.blowUpToBase I) ≅
      Over.mk (AlgebraicGeometry.blowUpToBase (I * D))) :
    (mulBaseChangeIso f I D e).hom ≫ pullback.snd f (AlgebraicGeometry.blowUpToBase (I * D)) =
      pullback.snd f (AlgebraicGeometry.blowUpToBase I) ≫ e.hom.left := by
  simp [mulBaseChangeIso, pullback.map]

/-- The inverse image under `Stacks.StrictTransform.mulBaseChangeIso` of the exceptional
preimage of the blowup in `I * D` is the exceptional preimage of the blowup in `I` together with
the inverse image of `Supp D` under `pr_X` followed by `f`. -/
public theorem mulBaseChangeIso_preimage_exceptionalPreimage (f : X ⟶ S)
    (I D : S.IdealSheafData)
    (e : Over.mk (AlgebraicGeometry.blowUpToBase I) ≅
      Over.mk (AlgebraicGeometry.blowUpToBase (I * D))) :
    (mulBaseChangeIso f I D e).hom.base ⁻¹'
        exceptionalPreimage f (AlgebraicGeometry.blowUpToBase (I * D))
          (AlgebraicGeometry.exceptionalIdeal (I * D)) =
      exceptionalPreimage f (AlgebraicGeometry.blowUpToBase I)
          (AlgebraicGeometry.exceptionalIdeal I) ∪
        (pullback.fst f (AlgebraicGeometry.blowUpToBase I)).base ⁻¹'
          (f.base ⁻¹' D.supportSet) := by
  have hw : e.hom.left ≫ AlgebraicGeometry.blowUpToBase (I * D) =
      AlgebraicGeometry.blowUpToBase I := by simpa using Over.w e.hom
  have hcomp : (mulBaseChangeIso f I D e).hom ≫
      pullback.snd f (AlgebraicGeometry.blowUpToBase (I * D)) ≫
        AlgebraicGeometry.blowUpToBase (I * D) =
      pullback.snd f (AlgebraicGeometry.blowUpToBase I) ≫
        AlgebraicGeometry.blowUpToBase I := by
    rw [← Category.assoc, mulBaseChangeIso_hom_snd, Category.assoc, hw]
  have hpt : ∀ {a b : baseChange f (AlgebraicGeometry.blowUpToBase I) ⟶ S}, a = b →
      ∀ x, a.base x = b.base x := fun h x => by rw [h]
  have hbase : ∀ x, (AlgebraicGeometry.blowUpToBase (I * D)).base
      ((pullback.snd f (AlgebraicGeometry.blowUpToBase (I * D))).base
        ((mulBaseChangeIso f I D e).hom.base x)) =
      (AlgebraicGeometry.blowUpToBase I).base
        ((pullback.snd f (AlgebraicGeometry.blowUpToBase I)).base x) := fun x => by
    simpa using hpt hcomp x
  have hcenter : ∀ x, (AlgebraicGeometry.blowUpToBase I).base
      ((pullback.snd f (AlgebraicGeometry.blowUpToBase I)).base x) =
      f.base ((pullback.fst f (AlgebraicGeometry.blowUpToBase I)).base x) := fun x => by
    simpa using (hpt pullback.condition x).symm
  ext x
  simp only [exceptionalPreimage, AlgebraicGeometry.exceptionalIdeal,
    Scheme.IdealSheafData.support_comap, Scheme.IdealSheafData.support_mul,
    Set.mem_preimage, Set.mem_union]
  change ((AlgebraicGeometry.blowUpToBase (I * D)).base
      ((pullback.snd f (AlgebraicGeometry.blowUpToBase (I * D))).base
        ((mulBaseChangeIso f I D e).hom.base x)) ∈ I.support ⊔ D.support) ↔ _
  rw [hbase x]
  change _ ↔ (((AlgebraicGeometry.blowUpToBase I).base
      ((pullback.snd f (AlgebraicGeometry.blowUpToBase I)).base x) ∈ I.support) ∨
    (f.base ((pullback.fst f (AlgebraicGeometry.blowUpToBase I)).base x) ∈ D.supportSet))
  rw [← hcenter x]
  exact Iff.rfl

/-- **Away from the exceptional divisor, the pullback of `F` to the base change of a blowup has
no nonzero sections supported over `Supp D`.** Over the complement of the exceptional preimage
the projection `pr_X` is an open immersion ([Stacks, Tag 02OS] part (1)), so there `pr_X^* F` is
a restriction of `F` and the hypothesis `hF` on `F` applies. -/
public theorem supportedSections_pullback_fst_eq_zero (f : X ⟶ S) (I D : S.IdealSheafData)
    (F : X.Modules)
    (hF : ∀ (U : X.Opens) (s : Γ(F, U)),
      s ∈ (supportedSectionsSubmodule (f.base ⁻¹' D.supportSet) F).toSubmodule.obj (op U) →
        s = 0)
    (U : (baseChange f (AlgebraicGeometry.blowUpToBase I)).Opens)
    (hU : (U : Set (baseChange f (AlgebraicGeometry.blowUpToBase I))) ∩
      exceptionalPreimage f (AlgebraicGeometry.blowUpToBase I)
        (AlgebraicGeometry.exceptionalIdeal I) = ∅)
    (s : Γ((Scheme.Modules.pullback
      (pullback.fst f (AlgebraicGeometry.blowUpToBase I))).obj F, U))
    (hs : s ∈ (supportedSectionsSubmodule
      ((pullback.fst f (AlgebraicGeometry.blowUpToBase I)).base ⁻¹' (f.base ⁻¹' D.supportSet))
      ((Scheme.Modules.pullback
        (pullback.fst f (AlgebraicGeometry.blowUpToBase I))).obj F)).toSubmodule.obj (op U)) :
    s = 0 := by
  have hUV : U ≤ exceptionalComplement f (AlgebraicGeometry.blowUpToBase I)
      (AlgebraicGeometry.exceptionalIdeal I) := fun x hx =>
    fun hxZ => (Set.disjoint_left.mp (Set.disjoint_iff_inter_eq_empty.mpr hU)) hx hxZ
  have hVoi : IsOpenImmersion
      ((exceptionalComplement f (AlgebraicGeometry.blowUpToBase I)
        (AlgebraicGeometry.exceptionalIdeal I)).ι ≫
          pullback.fst f (AlgebraicGeometry.blowUpToBase I)) :=
    isOpenImmersion_exceptionalComplement_ι_comp_fst f I
  have hoi : IsOpenImmersion (U.ι ≫ pullback.fst f (AlgebraicGeometry.blowUpToBase I)) := by
    rw [← Scheme.homOfLE_ι _ hUV, Category.assoc]
    exact IsOpenImmersion.comp _ _
  exact supportedSections_eq_zero_of_pullback_on_open _ _ F hF U s hs

/-- **[Stacks, Tag 080H] part (2).** Let `D` be an effective Cartier divisor on `S` and let `F`
be a sheaf of `𝒪_X`-modules with no nonzero local sections supported in `f^{-1}D`. Given an
isomorphism `e` of the blowup of `S` in `I` with the blowup of `S` in `I * D` over `S` — part (1)
of the tag — the induced isomorphism of the two base changes, specified by both its projections,
carries the strict transform of `F` for the centre `I * D` to the strict transform for the centre
`I`.

Part (1) of the tag, which supplies `e`, is not in the repository; see the implementation notes
of this file. Everything else here is unconditional, [Stacks, Tag 02OS] part (1) being the
instance `AlgebraicGeometry.isIso_blowUpToBase_restrict_compl_support`.

The hypothesis `_hD` that `D` is an effective Cartier divisor is the tag's, and is retained so
that the statement is the tag's; it is used only through `e`, which part (1) deduces from it, so
the conclusion in fact holds for any `D` admitting such an `e`. -/
@[stacks 080H "part (2): strict transforms of modules"]
public theorem exists_baseChange_iso_sheaf_iso_mul (f : X ⟶ S) (I D : S.IdealSheafData)
    (_hD : Stacks.Divisors.IsEffectiveCartierDivisor D) (F : X.Modules)
    (hF : ∀ (U : X.Opens) (s : Γ(F, U)),
      s ∈ (supportedSectionsSubmodule (f.base ⁻¹' D.supportSet) F).toSubmodule.obj (op U) →
        s = 0)
    (e : Over.mk (AlgebraicGeometry.blowUpToBase I) ≅
      Over.mk (AlgebraicGeometry.blowUpToBase (I * D))) :
    ∃ g : baseChange f (AlgebraicGeometry.blowUpToBase I) ≅
        baseChange f (AlgebraicGeometry.blowUpToBase (I * D)),
      (g.hom ≫ pullback.fst f (AlgebraicGeometry.blowUpToBase (I * D)) =
        pullback.fst f (AlgebraicGeometry.blowUpToBase I)) ∧
      (g.hom ≫ pullback.snd f (AlgebraicGeometry.blowUpToBase (I * D)) =
        pullback.snd f (AlgebraicGeometry.blowUpToBase I) ≫ e.hom.left) ∧
      Nonempty ((Scheme.Modules.pullback g.hom).obj
        (sheaf f (AlgebraicGeometry.blowUpToBase (I * D))
          (AlgebraicGeometry.exceptionalIdeal (I * D)) F) ≅
        sheaf f (AlgebraicGeometry.blowUpToBase I)
          (AlgebraicGeometry.exceptionalIdeal I) F) :=
  ⟨mulBaseChangeIso f I D e, mulBaseChangeIso_hom_fst f I D e,
    mulBaseChangeIso_hom_snd f I D e,
    exists_sheaf_iso_of_preimage_exceptionalPreimage_union f
      (AlgebraicGeometry.blowUpToBase I) (AlgebraicGeometry.blowUpToBase (I * D))
      (AlgebraicGeometry.exceptionalIdeal I) (AlgebraicGeometry.exceptionalIdeal (I * D)) F _
      (mulBaseChangeIso f I D e) (mulBaseChangeIso_hom_fst f I D e)
      (mulBaseChangeIso_preimage_exceptionalPreimage f I D e)
      (supportedSections_pullback_fst_eq_zero f I D F hF)⟩

end Stacks.StrictTransform

end
