module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescent
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtalePullbackSections
public import StacksFrontier.CategoryTheory.Sites.PullbackSectionsMateTerminal

/-!
# Descent of small étale sheaves and the sections of `π_S⁻¹F`

Let `B` be a big étale site, `S` one of its schemes, `F` a sheaf of sets on the small étale site
of `S` and `π_S⁻¹F` its inverse image on the big étale site over `S`. For a morphism
`h : X' ⟶ X` of schemes over `S`, this file shows that if the canonical functor from small étale
sheaves on `X` to descent data along `h` is an equivalence, then `π_S⁻¹F` satisfies the sheaf
condition for the single arrow `h`: the sequence
$$
(\pi_S^{-1}F)(X) \to (\pi_S^{-1}F)(X') \rightrightarrows (\pi_S^{-1}F)(X' \times_X X')
$$
is an equalizer. This is the step of the proofs of Stacks 0DDW and 0EW8 which uses, for a
proper surjective `h`, effective descent of small étale sheaves along `h` (Stacks 0GF0).

## Main definitions

* `AlgebraicGeometry.smallEtalePullbackHomEquivSections` — for `T` over `S` with structure
  morphism `f`, morphisms `f⁻¹⊤ ⟶ f⁻¹F` of small étale sheaves on `T` are the sections of
  `π_S⁻¹F` over `T`.

## Main results

* `AlgebraicGeometry.nonempty_presheafHom_iso` — for any small étale sheaf pullback system, its
  presheaf of morphisms `T ↦ (f⁻¹⊤ ⟶ f⁻¹F)` on the slice over `S` is isomorphic to `π_S⁻¹F`.
* `AlgebraicGeometry.isSheafFor_smallEtaleInverseImage_singleton_of_isEquivalence` — descent
  along `h` gives the sheaf condition of `π_S⁻¹F` for `h`.

## Implementation notes

Mathlib's `CategoryTheory.Pseudofunctor.bijective_toDescentData_map_iff` turns full faithfulness
of the descent functor at a pair `(M, N)` into the sheaf condition for the presheaf of morphisms
`T ↦ (M|_T ⟶ N|_T)`. With `M` the restriction of a terminal sheaf and `N` the restriction of
`F`, both from `S`, that presheaf is `π_S⁻¹F`: the inverse image of a terminal sheaf is terminal,
morphisms out of a terminal sheaf are global sections, and global sections of `f⁻¹F` are the
sections of `π_S⁻¹F` over `T` by the pullback formula of Stacks 09XN,
`AlgebraicGeometry.etaleInverseImageSectionsIso`. The compatibility with restriction maps is
`CategoryTheory.sheafPullbackSectionsRestriction_ΓEquivHomTerminal_symm`, which reads the
restriction maps of the pullback formula as inverse image followed by the canonical comparison of
iterated inverse images.

The isomorphism is proved for an arbitrary
`AlgebraicGeometry.SmallEtaleSheafPullbackSystem`: such a system is unfolded into its fields, and
the fields describing the fibres, the transition functors and the composition comparisons are
substituted, after which the presheaf of morphisms is computed directly.

## References

* [Stacks Project, Tag 0DDW](https://stacks.math.columbia.edu/tag/0DDW)
* [Stacks Project, Tag 0EW8](https://stacks.math.columbia.edu/tag/0EW8)
* [Stacks Project, Tag 0GF0](https://stacks.math.columbia.edu/tag/0GF0)
* [Stacks Project, Tag 09XN](https://stacks.math.columbia.edu/tag/09XN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u})

/-- The inverse image of a terminal small étale sheaf along a morphism of a big étale site is
terminal. -/
public def isTerminal_smallEtaleSheafPullback_terminal {S T : B.Scheme} (f : T ⟶ S) :
    IsTerminal (((smallEtaleBaseChange B f).sheafPullback (Type (u + 1))
      (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T.obj T.property)).obj
        (⊤_ Sheaf (SmallEtale.topology B S.obj S.property) (Type (u + 1)))) := by
  have : RepresentablyFlat (smallEtaleBaseChange B f) := flat_of_preservesFiniteLimits _
  exact terminalIsTerminal.isTerminalObj _ _

/-- For a scheme `T` over `S`, morphisms `f⁻¹⊤ ⟶ f⁻¹F` of small étale sheaves on `T` are the
sections of `π_S⁻¹F` over `T`: the inverse image of a terminal sheaf is terminal, morphisms out
of a terminal sheaf are global sections, and global sections of `f⁻¹F` are sections of `π_S⁻¹F`
by the pullback formula of Stacks 09XN. -/
public def smallEtalePullbackHomEquivSections (S : B.Scheme)
    (T : BigEtaleOver B S.obj S.property)
    (F : Sheaf (SmallEtale.topology B S.obj S.property) (Type (u + 1))) :
    (((smallEtaleBaseChange B T.hom).sheafPullback (Type (u + 1))
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.left.obj T.left.property)).obj
          (⊤_ Sheaf (SmallEtale.topology B S.obj S.property) (Type (u + 1))) ⟶
      ((smallEtaleBaseChange B T.hom).sheafPullback (Type (u + 1))
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.left.obj T.left.property)).obj F) ≃
    ((bigEtaleToSmallEtaleMorphism B S.obj S.property).inverseImage.obj F).obj.obj (op T) :=
  (Iso.homFromEquiv (terminalIsTerminal.uniqueUpToIso
      (isTerminal_smallEtaleSheafPullback_terminal B T.hom)).symm).trans
    ((Sheaf.ΓEquivHomTerminal.{u, u + 1, u + 1} _ _).symm.trans
      ((etaleInverseImageSectionsIso B S T).app F).symm.toEquiv)

/-- `AlgebraicGeometry.smallEtalePullbackHomEquivSections` is natural along `g : T' ⟶ T.left`:
restriction of sections of `π_S⁻¹F` along `Over.mk (g ≫ T.hom) ⟶ T` is inverse image along `g`
followed by the canonical comparison `g⁻¹f⁻¹ ≅ (g ≫ f)⁻¹`. -/
public theorem smallEtalePullbackHomEquivSections_naturality (S : B.Scheme)
    (T : BigEtaleOver B S.obj S.property) {T' : B.Scheme} (g : T' ⟶ T.left)
    (F : Sheaf (SmallEtale.topology B S.obj S.property) (Type (u + 1)))
    (φ : ((smallEtaleBaseChange B T.hom).sheafPullback (Type (u + 1))
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.left.obj T.left.property)).obj
          (⊤_ Sheaf (SmallEtale.topology B S.obj S.property) (Type (u + 1))) ⟶
      ((smallEtaleBaseChange B T.hom).sheafPullback (Type (u + 1))
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.left.obj T.left.property)).obj F) :
    smallEtalePullbackHomEquivSections B S (Over.mk (g ≫ T.hom)) F
        ((smallEtaleMorphism_comp_inverseImageIso B T' T.left S g T.hom).inv.app _ ≫
          ((smallEtaleBaseChange B g).sheafPullback (Type (u + 1))
            (SmallEtale.topology B T.left.obj T.left.property)
            (SmallEtale.topology B T'.obj T'.property)).map φ ≫
          (smallEtaleMorphism_comp_inverseImageIso B T' T.left S g T.hom).hom.app F) =
      ((bigEtaleToSmallEtaleMorphism B S.obj S.property).inverseImage.obj F).obj.map
        (Over.homMk g rfl : Over.mk (g ≫ T.hom) ⟶ T).op
        (smallEtalePullbackHomEquivSections B S T F φ) := by
  have hnat := ConcreteCategory.congr_hom
    (etaleInverseImageSectionsIso_naturality B S
      (Over.homMk g rfl : (Over.mk (g ≫ T.hom) : BigEtaleOver B S.obj S.property) ⟶ T) F)
  apply ((etaleInverseImageSectionsIso B S (Over.mk (g ≫ T.hom))).app F).toEquiv.injective
  simp only [smallEtalePullbackHomEquivSections, Equiv.trans_apply]
  simp only [ConcreteCategory.comp_apply] at hnat
  simp only [Iso.toEquiv_fun, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Iso.homFromEquiv_apply,
    Iso.symm_inv]
  rw [← hnat, Iso.inv_hom_id_app_apply, Iso.inv_hom_id_app_apply]
  let g' : (Over.mk (g ≫ T.hom) : BigEtaleOver B S.obj S.property) ⟶ T := Over.homMk g rfl
  let e := (smallEtaleBaseChange_compIso B T' T.left S g T.hom).val ≪≫
    eqToIso (congrArg (smallEtaleBaseChange B) (Over.w g'))
  have he : e = (smallEtaleBaseChange_compIso B T' T.left S g T.hom).val := by
    ext U
    simp [e]
  let u₀ := (terminalIsTerminal.uniqueUpToIso
        (isTerminal_smallEtaleSheafPullback_terminal B (g ≫ T.hom))).hom ≫
      (smallEtaleMorphism_comp_inverseImageIso B T' (Over.left T) S g (Over.hom T)).inv.app _ ≫
      ((smallEtaleBaseChange B g).sheafPullback (Type (u + 1))
        (SmallEtale.topology B T.left.obj T.left.property)
        (SmallEtale.topology B T'.obj T'.property)).map
          (terminalIsTerminal.uniqueUpToIso
            (isTerminal_smallEtaleSheafPullback_terminal B T.hom)).inv
  have hL : (Adjunction.leftAdjointCompIso
      ((smallEtaleBaseChange B T.hom).sheafAdjunctionContinuous (Type (u + 1))
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.left.obj T.left.property))
      ((smallEtaleBaseChange B g).sheafAdjunctionContinuous (Type (u + 1))
        (SmallEtale.topology B T.left.obj T.left.property)
        (SmallEtale.topology B T'.obj T'.property))
      ((smallEtaleBaseChange B (g ≫ T.hom)).sheafAdjunctionContinuous (Type (u + 1))
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T'.obj T'.property))
      (Functor.sheafPushforwardContinuousComp' e (Type (u + 1)) _ _ _)).hom.app F =
      (smallEtaleMorphism_comp_inverseImageIso B T' (Over.left T) S g (Over.hom T)).hom.app F := by
    rw [he]
    rfl
  refine Eq.trans ?_ (sheafPullbackSectionsRestriction_ΓEquivHomTerminal_symm
    (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T.left.obj T.left.property)
    (SmallEtale.topology B T'.obj T'.property) (smallEtaleBaseChange B T.hom)
    (smallEtaleBaseChange B g) (smallEtaleBaseChange B (g ≫ T.hom)) e F
    (SmallEtale.finalIsTerminal B T.left.obj T.left.property)
    (smallEtaleBaseChange_finalIsTerminal B g) (isTerminal_smallEtaleSheafPullback_terminal B g)
    ((terminalIsTerminal.uniqueUpToIso
      (isTerminal_smallEtaleSheafPullback_terminal B T.hom)).hom ≫ φ)
    u₀).symm
  rw [hL]
  congr 1
  simp only [u₀, Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_assoc]
  rfl

/-- The naturality of `AlgebraicGeometry.smallEtalePullbackHomEquivSections` along an arbitrary
morphism `Over.mk c ⟶ T` of schemes over `S`, with the identification of `(g ≫ T.hom)⁻¹` and
`c⁻¹` written as transport along `g ≫ T.hom = c`; the comparison on the terminal sheaf is
arbitrary, its source being terminal. -/
public theorem smallEtalePullbackHomEquivSections_naturality_of_eq (S : B.Scheme)
    (T : BigEtaleOver B S.obj S.property) {T' : B.Scheme} (c : T' ⟶ S) (g : T' ⟶ T.left)
    (w : g ≫ T.hom = c)
    (F : Sheaf (SmallEtale.topology B S.obj S.property) (Type (u + 1)))
    (φ : ((smallEtaleBaseChange B T.hom).sheafPullback (Type (u + 1))
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.left.obj T.left.property)).obj
          (⊤_ Sheaf (SmallEtale.topology B S.obj S.property) (Type (u + 1))) ⟶
      ((smallEtaleBaseChange B T.hom).sheafPullback (Type (u + 1))
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.left.obj T.left.property)).obj F)
    (E₁ : ((smallEtaleBaseChange B c).sheafPullback (Type (u + 1))
        (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T'.obj T'.property)).obj
          (⊤_ Sheaf (SmallEtale.topology B S.obj S.property) (Type (u + 1))) ⟶
      ((smallEtaleBaseChange B (g ≫ T.hom)).sheafPullback (Type (u + 1))
        (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T'.obj T'.property)).obj
          (⊤_ Sheaf (SmallEtale.topology B S.obj S.property) (Type (u + 1))))
    (E₂ : ((smallEtaleBaseChange B (g ≫ T.hom)).sheafPullback (Type (u + 1))
        (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T'.obj T'.property)).obj F ⟶
      ((smallEtaleBaseChange B c).sheafPullback (Type (u + 1))
        (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T'.obj T'.property)).obj F)
    (hE₂ : E₂ = eqToHom (by rw [w])) :
    smallEtalePullbackHomEquivSections B S (Over.mk c) F
        (E₁ ≫ (smallEtaleMorphism_comp_inverseImageIso B T' T.left S g T.hom).inv.app _ ≫
          ((smallEtaleBaseChange B g).sheafPullback (Type (u + 1))
            (SmallEtale.topology B T.left.obj T.left.property)
            (SmallEtale.topology B T'.obj T'.property)).map φ ≫
          (smallEtaleMorphism_comp_inverseImageIso B T' T.left S g T.hom).hom.app F ≫ E₂) =
      ((bigEtaleToSmallEtaleMorphism B S.obj S.property).inverseImage.obj F).obj.map
        (Over.homMk g w : Over.mk c ⟶ T).op
        (smallEtalePullbackHomEquivSections B S T F φ) := by
  subst w hE₂
  obtain rfl : E₁ = 𝟙 _ :=
    (isTerminal_smallEtaleSheafPullback_terminal B (g ≫ T.hom)).hom_ext _ _
  simp only [eqToHom_refl, Category.comp_id]
  exact smallEtalePullbackHomEquivSections_naturality B S T g F φ

/-- For any small étale sheaf pullback system on `B`, the presheaf of morphisms `T ↦ (f⁻¹⊤ ⟶ f⁻¹F)`
on the slice over `S` (Mathlib's `CategoryTheory.Pseudofunctor.presheafHom`) is isomorphic to
the presheaf underlying `π_S⁻¹F`. -/
public theorem nonempty_presheafHom_iso (Sys : SmallEtaleSheafPullbackSystem B) (S : B.Scheme)
    (F : Sheaf (SmallEtale.topology B S.obj S.property) (Type (u + 1))) :
    Nonempty (Sys.pseudofunctor.presheafHom
        ((eqToHom (Sys.fiber S).symm).toFunctor.obj
          (⊤_ Sheaf (SmallEtale.topology B S.obj S.property) (Type (u + 1))))
        ((eqToHom (Sys.fiber S).symm).toFunctor.obj F) ≅
      ((bigEtaleToSmallEtaleMorphism B S.obj S.property).inverseImage.obj F).obj) := by
  obtain ⟨P, fiber, pullback, canon⟩ := Sys
  obtain ⟨⟨⟨⟨obj, map⟩, map₂⟩, map₂_id, map₂_comp⟩, mapId, mapComp, a1, a2, a3, a4, a5⟩ := P
  have hobj : obj = fun (X : LocallyDiscrete B.Schemeᵒᵖ) =>
      Cat.of (Sheaf (SmallEtale.topology B X.as.unop.1 X.as.unop.property) (Type (u + 1))) := by
    funext X
    exact fiber X.as.unop
  subst hobj
  have hmap : @map = fun (X Y : LocallyDiscrete B.Schemeᵒᵖ) (f : X ⟶ Y) =>
      ((smallEtaleBaseChange B f.as.unop).sheafPullback (Type (u + 1))
        (SmallEtale.topology B X.as.unop.1 X.as.unop.property)
        (SmallEtale.topology B Y.as.unop.1 Y.as.unop.property)).toCatHom := by
    funext X Y f
    obtain ⟨f⟩ := f
    have h := pullback f.unop
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at h
    exact h
  subst hmap
  have hcomp : @mapComp = fun (X Y Z : LocallyDiscrete B.Schemeᵒᵖ) (f : X ⟶ Y) (g : Y ⟶ Z) =>
      Cat.Hom.isoMk (smallEtaleMorphism_comp_inverseImageIso B Z.as.unop Y.as.unop X.as.unop
        g.as.unop f.as.unop).symm := by
    funext X Y Z f g
    obtain ⟨f⟩ := f
    obtain ⟨g⟩ := g
    exact eq_of_heq (canon g.unop f.unop)
  subst hcomp
  have hmap₂ : ∀ {X Y : LocallyDiscrete B.Schemeᵒᵖ} {f f' : X ⟶ Y} (h : f = f') M,
      (map₂ (eqToHom h)).toNatTrans.app M = eqToHom (by rw [h]) := by
    intro X Y f f' h M
    subst h
    rw [eqToHom_refl, eqToHom_refl]
    exact congrArg (fun t => t.toNatTrans.app M) (map₂_id f)
  refine ⟨NatIso.ofComponents (fun T => (smallEtalePullbackHomEquivSections B S T.unop F).toIso)
    ?_⟩
  rintro ⟨T₁⟩ ⟨T₂⟩ ⟨g⟩
  ext φ
  simp only [TypeCat.Fun.toFun_apply, ConcreteCategory.comp_apply, Pseudofunctor.presheafHom_map,
    TypeCat.ofHom_apply]
  refine Eq.trans (congrArg (smallEtalePullbackHomEquivSections B S T₂ F) ?_)
    (smallEtalePullbackHomEquivSections_naturality_of_eq B S T₁ T₂.hom g.left
      (Over.w g) F φ
      ((map₂ (eqToHom (congrArg (fun x => x.op.toLoc) (Over.w g).symm :
        T₂.hom.op.toLoc = T₁.hom.op.toLoc ≫ g.left.op.toLoc))).toNatTrans.app
          (⊤_ Sheaf (SmallEtale.topology B S.obj S.property) (Type (u + 1))))
      ((map₂ (eqToHom (congrArg (fun x => x.op.toLoc) (Over.w g) :
        T₁.hom.op.toLoc ≫ g.left.op.toLoc = T₂.hom.op.toLoc))).toNatTrans.app F)
      (hmap₂ _ _))
  dsimp only [Pseudofunctor.LocallyDiscreteOpToCat.pullHom, Pseudofunctor.mapComp']
  simp only [Iso.trans_hom, Iso.trans_inv, Cat.Hom₂.comp_app, PrelaxFunctor.map₂Iso_hom,
    PrelaxFunctor.map₂Iso_inv, eqToIso.hom, eqToIso.inv, Cat.Hom.isoMk_hom, Cat.Hom.isoMk_inv,
    Iso.symm_hom, Iso.symm_inv, Category.assoc]
  rfl

/-- **Descent gives the sheaf condition along one arrow.** If descent of small étale sheaves along
`h.left` is effective, then `π_S⁻¹F` satisfies the sheaf condition for the single arrow
`h : X' ⟶ X` of the big étale category over `S`. Only full faithfulness of the descent functor
is used. -/
public theorem isSheafFor_smallEtaleInverseImage_singleton_of_isEquivalence (S : B.Scheme)
    (F : Sheaf (SmallEtale.topology B S.obj S.property) (Type (u + 1)))
    {X X' : BigEtaleOver B S.obj S.property} (h : X' ⟶ X)
    (hdesc : (smallEtaleSheafDescentFunctor B h.left).IsEquivalence) :
    Presieve.IsSheafFor ((bigEtaleToSmallEtaleMorphism B S.obj S.property).inverseImage.obj F).obj
      (Presieve.singleton h) := by
  let Sys := smallEtaleSheafPullbackSystem B
  let P := Sys.pseudofunctor
  let E := (eqToHom (Sys.fiber X.left).symm).toFunctor
  let ES := (eqToHom (Sys.fiber S).symm).toFunctor
  have hE : E.IsEquivalence :=
    (Cat.equivOfIso (eqToIso (Sys.fiber X.left).symm)).isEquivalence_functor
  have hG : (P.toDescentData (fun _ : Unit ↦ h.left)).IsEquivalence := by
    have : (E ⋙ P.toDescentData (fun _ : Unit ↦ h.left)).IsEquivalence := hdesc
    exact Functor.isEquivalence_of_comp_left E _
  have hbij : ∀ M N : P.obj (.mk (op X.left)),
      Function.Bijective ((P.toDescentData (fun _ : Unit ↦ h.left)).map : (M ⟶ N) → _) :=
    fun M N => (Functor.FullyFaithful.ofFullyFaithful _).map_bijective M N
  let M := (P.map X.hom.op.toLoc).toFunctor.obj
    (ES.obj (⊤_ Sheaf (SmallEtale.topology B S.obj S.property) (Type (u + 1))))
  let N := (P.map X.hom.op.toLoc).toFunctor.obj (ES.obj F)
  have h1 := (Pseudofunctor.bijective_toDescentData_map_iff (fun _ : Unit ↦ h.left) M N).1
    (hbij M N)
  rw [← Presieve.isSheafFor_iff_of_iso (P.overMapCompPresheafHomIso _ _ X.hom),
    Presieve.isSheafFor_iff_generate,
    Presieve.isSheafFor_over_map_op_comp_iff X.hom _ _
      (Over.isoMk (Iso.refl _) (by simp) : (Over.map X.hom).obj (Over.mk (𝟙 X.left)) ≅ X)] at h1
  obtain ⟨ψ⟩ := nonempty_presheafHom_iso B Sys S F
  rw [Presieve.isSheafFor_iff_of_iso ψ] at h1
  rw [Presieve.isSheafFor_iff_generate]
  convert h1 using 2
  apply le_antisymm
  · rw [Sieve.generate_le_iff]
    rintro _ _ ⟨⟩
    refine ⟨Over.mk h.left, Over.homMk h.left (by simp),
      Over.homMk (𝟙 X'.left) (by simp [Over.w h]),
      ⟨_, 𝟙 _, _, Presieve.ofArrows.mk (), by simp⟩, ?_⟩
    apply Over.OverMorphism.ext
    simp
  · rintro Z k ⟨W, a, b, ⟨V, c, d, hd, rfl⟩, hab⟩
    obtain ⟨⟩ := hd
    refine ⟨_, b ≫ (Over.map X.hom).map c ≫ Over.homMk (𝟙 X'.left) (by simp [Over.w h]), h,
      Presieve.singleton.mk, ?_⟩
    apply Over.OverMorphism.ext
    simpa using (congrArg CommaMorphism.left hab).symm

end AlgebraicGeometry

end
