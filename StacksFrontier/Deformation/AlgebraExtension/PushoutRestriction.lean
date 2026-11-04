module

public import StacksFrontier.Deformation.AlgebraExtension.SiteEquivalence

/-!
# Pushout of extensions commutes with restriction to a dense subsite

Let `G : 𝒟 ⥤ 𝒞` be a dense subsite reaching every object of `𝒞` up to isomorphism, and let
`φ : ℳ ⟶ 𝒩` be a morphism of `𝒪`-modules on `𝒞` with restriction `φ' : ℳ' ⟶ 𝒩'` to `𝒟`. If `F`
and `F'` are pushout functors along `φ` and along `φ'`, then restricting and pushing out agree:
`R_ℳ ⋙ F' ≅ F ⋙ R_𝒩`. The comparison `F'(R P) ⟶ R(F P)` is the factorisation of the restriction of
`P ⟶ F P` through `R P ⟶ F'(R P)`; it is an isomorphism because on `𝒟` every morphism of
extensions by a fixed module is one (the short five lemma: it is injective and locally surjective
on sections).

Consequently, when restriction is an equivalence of extension categories — for instance along
the inverse of an equivalence of sites — `F` is an equivalence as soon as `F'` is. This transfers
[Stacks Project, Tag 0D3P] from a site in one universe to an equivalent site.

## Main results

* `Deformation.AlgebraExtension.isIso_of_mapAlong`: every morphism of extensions by a fixed module
  is an isomorphism.
* `Deformation.AlgebraExtension.IsPushoutFunctor.restrictIso`: `R_ℳ ⋙ F' ≅ F ⋙ R_𝒩`.
* `Deformation.AlgebraExtension.IsPushoutFunctor.isEquivalence_of_siteRestriction`: `F` is an
  equivalence once `F'` is, on equivalent sites.

## References

* [Stacks Project, Tag 0D3P](https://stacks.math.columbia.edu/tag/0D3P)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v₁ w₁ v₂ w₂

namespace Deformation.AlgebraExtension

section Groupoid

variable {C : Type v₁} [Category.{w₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] [HasWeakSheafify J CommRingCat.{u}]
  [J.WEqualsLocallyBijective CommRingCat.{u}] [J.HasSheafCompose (forget CommRingCat.{u})]
  {A O : Sheaf J CommRingCat.{u}} {a : A ⟶ O}
  {M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)}

omit [HasWeakSheafify J CommRingCat.{u}] [J.WEqualsLocallyBijective CommRingCat.{u}] in
/-- **Every morphism of extensions by a fixed module is an isomorphism**: it is injective on
sections and locally surjective, by the short five lemma on the two ideal rows. -/
theorem isIso_of_mapAlong {P Q : AlgebraExtension a M} (f : P ⟶ Q) : IsIso f :=
  have : IsIso f.hom := (Sheaf.isLocallyBijective_iff_isIso _).1
    ⟨(Sheaf.isLocallyInjective_iff_injective _).2
      (f.injective_app fun _ => Function.injective_id),
      f.isLocallySurjective fun _ => Function.surjective_id⟩
  isIso_of_isIso_hom f

end Groupoid

section Restriction

variable {C : Type v₁} [Category.{w₁} C] {D : Type v₂} [Category.{w₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {G : D ⥤ C}
  [G.IsContinuous K J] [G.IsCocontinuous K J]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasWeakSheafify K CommRingCat.{u}] [K.WEqualsLocallyBijective CommRingCat.{u}]
  [K.HasSheafCompose (forget CommRingCat.{u})]
  {A O : Sheaf J CommRingCat.{u}} {a : A ⟶ O} {A' O' : Sheaf K CommRingCat.{u}} {a' : A' ⟶ O'}
  {M N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)}
  {M' N' : SheafOfModules.{u} ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj O')}
  {c : RingComparison (G := G) a a'} {cM : ModuleComparison c.ω M M'}
  {cN : ModuleComparison c.ω N N'} {φ : M ⟶ N} {φ' : M' ⟶ N'}
  (hφ : ∀ (V : Dᵒᵖ) (m : M'.val.obj V),
    cN.μ V (φ'.val.app V m) = φ.val.app (G.op.obj V) (cM.μ V m))
  {F : AlgebraExtension a M ⥤ AlgebraExtension a N} (hF : IsPushoutFunctor φ F)
  {F' : AlgebraExtension a' M' ⥤ AlgebraExtension a' N'} (hF' : IsPushoutFunctor φ' F')

include hφ hF hF' in
omit [HasWeakSheafify K CommRingCat.{u}] [K.WEqualsLocallyBijective CommRingCat.{u}]
  [K.HasSheafCompose (forget CommRingCat.{u})] in
/-- The comparison `F'(R P) ⟶ R(F P)`: the factorisation of the restriction of `P ⟶ F P` through
`R P ⟶ F'(R P)`. -/
theorem IsPushoutFunctor.exists_restrictComparison (P : AlgebraExtension a M) :
    ∃ k : F'.obj ((restrictViaFunctor a' M' c cM).obj P) ⟶
        (restrictViaFunctor a' N' c cN).obj (F.obj P),
      (hF'.ι _).hom ≫ k.hom = (ringRes K G).map (hF.ι P).hom :=
  (hF'.desc_unique _ _ (MapAlong.restrictVia c cM cN hφ (hF.ι P))).exists

/-- The comparison `F'(R P) ⟶ R(F P)`. -/
noncomputable def IsPushoutFunctor.restrictComparison (P : AlgebraExtension a M) :
    F'.obj ((restrictViaFunctor a' M' c cM).obj P) ⟶
      (restrictViaFunctor a' N' c cN).obj (F.obj P) :=
  (hF.exists_restrictComparison hφ hF' P).choose

omit [HasWeakSheafify K CommRingCat.{u}] [K.WEqualsLocallyBijective CommRingCat.{u}]
  [K.HasSheafCompose (forget CommRingCat.{u})] in
/-- The defining property of `restrictComparison`: precomposed with `R P ⟶ F'(R P)` it is the
restriction of `P ⟶ F P`. -/
theorem IsPushoutFunctor.restrictComparison_spec (P : AlgebraExtension a M) :
    (hF'.ι _).hom ≫ (hF.restrictComparison hφ hF' P).hom = (ringRes K G).map (hF.ι P).hom :=
  (hF.exists_restrictComparison hφ hF' P).choose_spec

/-- **Restricting and pushing out agree**: `R_ℳ ⋙ F' ≅ F ⋙ R_𝒩`. -/
noncomputable def IsPushoutFunctor.restrictIso :
    restrictViaFunctor a' M' c cM ⋙ F' ≅ F ⋙ restrictViaFunctor a' N' c cN :=
  NatIso.ofComponents
    (fun P => @asIso _ _ _ _ (hF.restrictComparison hφ hF' P) (isIso_of_mapAlong _))
    fun {P P'} g => by
      let h : MapAlong φ' ((restrictViaFunctor a' M' c cM).obj P)
          ((restrictViaFunctor a' N' c cN).obj (F.obj P')) :=
        MapAlong.restrictVia c cM cN hφ ((g : MapAlong (𝟙 M) P P').comp (hF.ι P') (by simp))
      refine (hF'.desc_unique _ _ h).unique ?_ ?_
      · change (hF'.ι _).hom ≫ (F'.map ((restrictViaFunctor a' M' c cM).map g)).hom ≫
          (hF.restrictComparison hφ hF' P').hom = (ringRes K G).map (g.hom ≫ (hF.ι P').hom)
        exact (Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ (hF.restrictComparison hφ hF' P').hom) (hF'.naturality _)).trans
            ((Category.assoc _ _ _).trans
              ((congrArg ((ringRes K G).map g.hom ≫ ·)
                (hF.restrictComparison_spec hφ hF' P')).trans
                ((ringRes K G).map_comp _ _).symm)))
      · change (hF'.ι _).hom ≫ (hF.restrictComparison hφ hF' P).hom ≫
          (ringRes K G).map (F.map g).hom = (ringRes K G).map (g.hom ≫ (hF.ι P').hom)
        exact (Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ (ringRes K G).map (F.map g).hom)
            (hF.restrictComparison_spec hφ hF' P)).trans
            (((ringRes K G).map_comp _ _).symm.trans
              (congrArg (ringRes K G).map (hF.naturality g))))

include hφ hF hF' in
omit [HasWeakSheafify K CommRingCat.{u}] [K.WEqualsLocallyBijective CommRingCat.{u}] in
/-- **A pushout functor is an equivalence once its restriction is**, when restriction is an
equivalence on both sides. -/
theorem IsPushoutFunctor.isEquivalence_of_restrict
    [(restrictViaFunctor a' M' c cM).IsEquivalence] [(restrictViaFunctor a' N' c cN).IsEquivalence]
    [F'.IsEquivalence] : F.IsEquivalence := by
  have : (F ⋙ restrictViaFunctor a' N' c cN).IsEquivalence :=
    Functor.isEquivalence_of_iso (IsPushoutFunctor.restrictIso hφ hF hF')
  exact Functor.isEquivalence_of_comp_right F (restrictViaFunctor a' N' c cN)

end Restriction

end Deformation.AlgebraExtension

end
