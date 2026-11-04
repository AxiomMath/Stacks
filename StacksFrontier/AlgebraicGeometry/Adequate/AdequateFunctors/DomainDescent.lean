module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.CechExactFromSheaf
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.DomainRestriction

/-!
# Descent of adequate functors over the algebras of a site

[Stacks, Tag 06VH], `AdequateFunctor.isAdequate_of_descent`, descends adequacy of a
module-valued functor along a ring map `f : A → A'` from the Čech condition. It is stated on the
full domain `𝟭 (CommAlgCat A)` of *all* `A`-algebras, while the functor that consumes it — the
affine-section functor of a sheaf of modules on a big site — is defined only on the algebras
whose spectra belong to the site. This module carries the descent across that change of domain.

## Main definitions

* `AdequateFunctor.SiteBaseChangeClosed` — the hypothesis that makes the port possible: the
  algebras of the site are closed under base change along `f`, so that `B ↦ B ⊗_A A'` is an
  endofunctor of them. It is a size statement, and it is discharged geometrically; nothing here
  depends on how.
* `AdequateFunctor.cechBaseChangeOn`, `AdequateFunctor.cechUnitOn`,
  `AdequateFunctor.cechRingMapOn`, `AdequateFunctor.cechOnceOn`,
  `AdequateFunctor.cechTwiceOn`, `AdequateFunctor.cechAugmentationOn`,
  `AdequateFunctor.cechMapInnerOn`, `AdequateFunctor.cechMapOuterOn` and
  `AdequateFunctor.cechDifferentialOn` — the Čech diagram of `AdequateFunctor.Descent` on the
  site's domain of algebras.
* `AdequateFunctor.baseChangeFunctorOn`, `AdequateFunctor.baseChangeRingHomOn` and
  `AdequateFunctor.pushforwardOn` — the pushforward of [Stacks, Tag 06VA] on that domain.

## Main results

* `AdequateFunctor.isAdequate_pushforwardOn` — [Stacks, Tag 06VA] on the site's domain of
  algebras.
* `AdequateFunctor.isAdequate_cechOnceOn` — the degree-one Čech term of a functor on the site's
  algebras is adequate as soon as its restriction to the `A'`-algebras of the site is.
* `AdequateFunctor.cechAugmentationOnKernelIso` — under the Čech condition the augmentation
  exhibits the functor as the kernel of its Čech differential.
* `AdequateFunctor.isAdequate_of_descent_on` — **[Stacks, Tag 06VH] on the site's domain of
  algebras.** Adequacy of the functor follows from adequacy of its restriction to the
  `A'`-algebras of the site, the Čech condition `AdequateFunctor.CechExactOn`, and closure of
  adequacy under kernels on the domain.

## Implementation notes

**The domain is a full subcategory, and that is what makes the port cheap.** Every object and
every morphism of `AdequateFunctor.AlgebrasInSite` is one of `CommAlgCat`, so the whole Čech
*algebra* of `AdequateFunctor.Descent` — the base change, its unit, the inclusion of `A'`, and
the fact that the base change is the binary coproduct of `B` and `A'` — transports by
`CategoryTheory.ObjectProperty.lift` and `CategoryTheory.ObjectProperty.homMk` with no content
added: `cechBaseChangeOn ⋙ siteAlgebraInclusion = siteAlgebraInclusion ⋙ cechBaseChange`
holds definitionally, and the cofan of a site algebra *is* `AdequateFunctor.cechCofan` of the
underlying algebra, so `AdequateFunctor.cechCofanIsColimit` is reused rather than reproved.
That is why `cechBaseInclusion`, `cechCofan` and `cechCofanIsColimit` are public in
`AdequateFunctor.Descent`.

**What does have content is the adequacy of the two Čech terms**, and it is supplied by
[Stacks, Tag 06VA] on the domain, `isAdequate_pushforwardOn`. That in turn is the full-domain
`AdequateFunctor.isAdequate_pushforward` sandwiched between
`AdequateFunctor.IsAdequate.exists_extension` — which says an adequate functor on any domain is
the restriction of one on all algebras — and `AdequateFunctor.IsAdequate.restrictDomain`, the
same sandwich that carries [Stacks, Tag 06V9] across in
`AdequateFunctor.IsAdequate.restrictBaseOn`. The two reindexings commute on the nose, which is
`pushforwardOn_restrictDomain`.

**The two scalar comparisons are never compared against each other.** `cechOnceOn` is the
pushforward along `cechRingMapOn`, the unit of base change, because that is what makes the
augmentation `F.map ((cechUnitOn ·).app _)` type-correct; `pushforwardOn` is the pushforward
along `baseChangeRingHomOn`, the pushout injection. The two agree definitionally, but a `rfl`
pitting `cechOnceOn F` against `pushforwardOn f (restrictFunctorOn f P F)` exhausts the
elaborator's heartbeats, exactly as the analogous comparison does on the full domain. So the
comparison is made one object at a time inside `cechOnceOnIsoPushforwardOn`, which is the
transcription of `AdequateFunctor.cechOnceIsoPushforward`.

The base ring and the algebras live in one universe here, as they do in
`AdequateFunctor.Descent`: on the geometric side the three universes of the domain machinery
collapse to the universe of the schemes.

## References

* [Stacks Project, Tag 06VH](https://stacks.math.columbia.edu/tag/06VH)
* [Stacks Project, Tag 06VA](https://stacks.math.columbia.edu/tag/06VA)
* [Stacks Project, Tag 06V9](https://stacks.math.columbia.edu/tag/06V9)
* [Stacks Project, Tag 06Z3](https://stacks.math.columbia.edu/tag/06Z3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe w u u₁ v₁

namespace AdequateFunctor

variable {A A' : Type u} [CommRing A] [CommRing A'] (f : A →+* A')
  (P : ObjectProperty Scheme.{u})

/-! ### Base change as an endofunctor of the site algebras -/

/-- The algebras of the site are closed under base change along `f : A → A'`: whenever
`Spec B` belongs to the site, so does `Spec (B ⊗_A A')`.

This is a condition on the chosen category of schemes alone — on sizes — and it is the one
hypothesis that the descent of [Stacks, Tag 06VH] needs in order to be stated on the site's
domain of algebras at all, since the Čech diagram of a site algebra must again consist of site
algebras. -/
abbrev SiteBaseChangeClosed : Prop :=
  ∀ B : AlgebrasInSite.{u, u} A P,
    algebraInSite.{u, u} A P ((cechBaseChange f).obj B.obj)

variable (hcl : SiteBaseChangeClosed f P)

/-- `AdequateFunctor.cechBaseChange` as an endofunctor of the algebras of the site. -/
def cechBaseChangeOn :
    AlgebrasInSite.{u, u} A P ⥤ AlgebrasInSite.{u, u} A P :=
  ObjectProperty.lift _ (siteAlgebraInclusion.{u, u} A P ⋙ cechBaseChange f) hcl

/-- Base change along `f` carries the `A`-algebras of the site to the `A'`-algebras of the
site: belonging to the site is a condition on the underlying ring, which
`AdequateFunctor.restrictAlgebras` does not change. -/
def baseChangeFunctorOn :
    AlgebrasInSite.{u, u} A P ⥤ AlgebrasInSite.{u, u} A' P :=
  ObjectProperty.lift _ (siteAlgebraInclusion.{u, u} A P ⋙ baseChangeFunctor f) hcl

/-- Base change on the site algebras is base change of algebras, on the nose. -/
theorem cechBaseChangeOn_comp_siteAlgebraInclusion :
    cechBaseChangeOn f P hcl ⋙ siteAlgebraInclusion.{u, u} A P =
      siteAlgebraInclusion.{u, u} A P ⋙ cechBaseChange f := rfl

/-- The unit `B ⟶ B ⊗_A A'` on the algebras of the site. -/
def cechUnitOn : 𝟭 (AlgebrasInSite.{u, u} A P) ⟶ cechBaseChangeOn f P hcl where
  app B := ObjectProperty.homMk ((cechUnit f).app B.obj)
  naturality _ _ g := ObjectProperty.hom_ext (P := algebraInSite.{u, u} A P)
    ((cechUnit f).naturality g.hom)

/-- The unit on the site algebras is the unit of base change. -/
@[simp] theorem siteAlgebraInclusion_map_cechUnitOn_app (B : AlgebrasInSite.{u, u} A P) :
    (siteAlgebraInclusion.{u, u} A P).map ((cechUnitOn f P hcl).app B) =
      (cechUnit f).app B.obj := rfl

/-- The unit map into the base-changed algebra, on the site algebras. -/
def cechRingMapOn :
    algebraRingDiagramOn.{u} (siteAlgebraInclusion.{u, u} A P) ⟶
      (cechBaseChangeOn f P hcl).op.op ⋙
        algebraRingDiagramOn.{u} (siteAlgebraInclusion.{u, u} A P) :=
  Functor.whiskerLeft (siteAlgebraInclusion.{u, u} A P).op.op (cechRingMap f)

/-- The injection of an algebra of the site into its base change, on the site algebras. -/
def baseChangeRingHomOn :
    algebraRingDiagramOn.{u} (siteAlgebraInclusion.{u, u} A P) ⟶
      (baseChangeFunctorOn f P hcl).op.op ⋙
        algebraRingDiagramOn.{u} (siteAlgebraInclusion.{u, u} A' P) :=
  Functor.whiskerLeft (siteAlgebraInclusion.{u, u} A P).op.op (baseChangeRingHom f)

/-- The functor `B ↦ F(B ⊗_A A')` on the algebras of the site, the degree-one term of the Čech
diagram of `F` there. -/
abbrev cechOnceOn (F : ModuleValuedFunctorOn.{w, u} (siteAlgebraInclusion.{u, u} A P)) :
    ModuleValuedFunctorOn.{w, u} (siteAlgebraInclusion.{u, u} A P) :=
  (PresheafOfModules.pushforward (cechRingMapOn f P hcl)).obj F

/-- The functor `B ↦ F(B ⊗_A A' ⊗_A A')` on the algebras of the site, the degree-two term of
the Čech diagram of `F` there. -/
abbrev cechTwiceOn (F : ModuleValuedFunctorOn.{w, u} (siteAlgebraInclusion.{u, u} A P)) :
    ModuleValuedFunctorOn.{w, u} (siteAlgebraInclusion.{u, u} A P) :=
  cechOnceOn f P hcl (cechOnceOn f P hcl F)

/-- The functor `B ↦ F'(B ⊗_A A')` on the algebras of the site: the pushforward of
[Stacks, Tag 06VA] there. -/
abbrev pushforwardOn (F' : ModuleValuedFunctorOn.{w, u} (siteAlgebraInclusion.{u, u} A' P)) :
    ModuleValuedFunctorOn.{w, u} (siteAlgebraInclusion.{u, u} A P) :=
  (PresheafOfModules.pushforward (baseChangeRingHomOn f P hcl)).obj F'

/-! ### Tag 06VA between two domains of algebras -/

section Between

variable (P' : ObjectProperty Scheme.{u})
  (hcl' : ∀ B : AlgebrasInSite.{u, u} A P,
    algebraInSite.{u, u} A' P' ((baseChangeFunctor f).obj B.obj))

/-- Base change along `f : A ⟶ A'`, from the `A`-algebras whose spectra satisfy `P` to the
`A'`-algebras whose spectra satisfy a possibly different property `P'`, granted that base change
carries the former into the latter. This is the shape in which the pushforward of
[Stacks, Tag 06VA] occurs when the two algebras belong to two different chosen big sites. -/
def baseChangeFunctorBetween :
    AlgebrasInSite.{u, u} A P ⥤ AlgebrasInSite.{u, u} A' P' :=
  ObjectProperty.lift _ (siteAlgebraInclusion.{u, u} A P ⋙ baseChangeFunctor f) hcl'

/-- The injection `B ⟶ B ⊗_A A'` of ring diagrams, between the two domains. -/
def baseChangeRingHomBetween :
    algebraRingDiagramOn.{u} (siteAlgebraInclusion.{u, u} A P) ⟶
      (baseChangeFunctorBetween f P P' hcl').op.op ⋙
        algebraRingDiagramOn.{u} (siteAlgebraInclusion.{u, u} A' P') :=
  Functor.whiskerLeft (siteAlgebraInclusion.{u, u} A P).op.op (baseChangeRingHom f)

/-- The functor `B ↦ F'(B ⊗_A A')` from the `A'`-algebras of `P'` to the `A`-algebras of `P`. -/
abbrev pushforwardBetween
    (F' : ModuleValuedFunctorOn.{w, u} (siteAlgebraInclusion.{u, u} A' P')) :
    ModuleValuedFunctorOn.{w, u} (siteAlgebraInclusion.{u, u} A P) :=
  (PresheafOfModules.pushforward (baseChangeRingHomBetween f P P' hcl')).obj F'

/-- **[Stacks, Tag 06VA] between two domains of algebras.** If `F'` is an adequate module-valued
functor on the `A'`-algebras whose spectra satisfy `P'`, and base change along `f : A ⟶ A'`
carries the `A`-algebras whose spectra satisfy `P` into those, then `B ↦ F'(B ⊗_A A')` is an
adequate module-valued functor on the `A`-algebras whose spectra satisfy `P`. As for
`AdequateFunctor.isAdequate_pushforwardOn`, which is the case `P' = P`, the tag for all algebras is
sandwiched between `AdequateFunctor.IsAdequate.exists_extension` and
`AdequateFunctor.IsAdequate.restrictDomain`. -/
theorem isAdequate_pushforwardBetween
    (F' : ModuleValuedFunctorOn.{max u w, u} (siteAlgebraInclusion.{u, u} A' P'))
    (hF' : IsAdequate.{max u w, u} (siteAlgebraInclusion.{u, u} A' P') F') :
    IsAdequate.{max u w, u} (siteAlgebraInclusion.{u, u} A P)
      (pushforwardBetween f P P' hcl' F') := by
  obtain ⟨G', hG', ⟨eG⟩⟩ :=
    IsAdequate.exists_extension.{max u w, u} (siteAlgebraInclusion.{u, u} A' P') F' hF'
  refine (IsAdequate.restrictDomain.{max u w, u} (siteAlgebraInclusion.{u, u} A P) (𝟭 _) _
    (isAdequate_pushforward.{u, max u w} f G' hG')).of_iso ?_
  exact (PresheafOfModules.pushforward (baseChangeRingHomBetween f P P' hcl')).mapIso
    ((presheafOfModulesUliftIso.{u, max u w}
      (algebraRingDiagramOn.{u} (siteAlgebraInclusion.{u, u} A' P')) F').symm ≪≫ eG)

end Between

/-! ### Tag 06VA on the algebras of the site -/

/-- Pushing forward along base change and shrinking the domain to the site algebras commute, on
the nose: both read a module-valued functor on all `A'`-algebras at `B ⊗_A A'`, for `B` an
algebra of the site. -/
theorem pushforwardOn_restrictDomain (G' : ModuleValuedFunctor.{w, u} A') :
    pushforwardOn f P hcl
        ((restrictDomain.{w, u} (siteAlgebraInclusion.{u, u} A' P) (𝟭 _)).obj G') =
      (restrictDomain.{w, u} (siteAlgebraInclusion.{u, u} A P) (𝟭 _)).obj
        (pushforward f G') := rfl

/-- **[Stacks, Tag 06VA] on the site's domain of algebras.** If `F'` is an adequate
module-valued functor on the `A'`-algebras of the site, then `B ↦ F'(B ⊗_A A')` is an adequate
module-valued functor on the `A`-algebras of the site.

`AdequateFunctor.IsAdequate.exists_extension` presents `F'` as the restriction of an adequate
functor `G'` on *all* `A'`-algebras, `AdequateFunctor.isAdequate_pushforward` pushes
`G'` forward, and `AdequateFunctor.IsAdequate.restrictDomain` shrinks the domain again; the two
reindexings commute by `AdequateFunctor.pushforwardOn_restrictDomain`. -/
theorem isAdequate_pushforwardOn
    (F' : ModuleValuedFunctorOn.{max u w, u} (siteAlgebraInclusion.{u, u} A' P))
    (hF' : IsAdequate.{max u w, u} (siteAlgebraInclusion.{u, u} A' P) F') :
    IsAdequate.{max u w, u} (siteAlgebraInclusion.{u, u} A P)
      (pushforwardOn f P hcl F') :=
  isAdequate_pushforwardBetween f P P hcl F' hF'

/-! ### The degree-one Čech term is that pushforward -/

/-- Reindexing a module-valued functor on the `A`-algebras of the site to the `A'`-algebras of
the site, along `AdequateFunctor.siteRestrictAlgebras`. This is restriction of the base ring
with no change of scalars interposed, the shape in which the Čech term of `F` is literally a
pushforward. -/
abbrev restrictZeroOn :
    ModuleValuedFunctorOn.{w, u} (siteAlgebraInclusion.{u, u} A P) ⥤
      ModuleValuedFunctorOn.{w, u} (siteAlgebraInclusion.{u, u} A' P) :=
  restrictDomain.{w, u} (siteRestrictAlgebras.{u, u, u} f P)
    (siteAlgebraInclusion.{u, u} A P)

/-- Reindexing and restricting the base ring differ by a restriction of scalars along the
identity, which `ModuleCat.restrictScalarsId'App` undoes. This is
`AdequateFunctor.restrictFunctorIsoPushforwardZero` on the site's domain of algebras. -/
def restrictZeroOnIso (F : ModuleValuedFunctorOn.{w, u} (siteAlgebraInclusion.{u, u} A P)) :
    (restrictZeroOn.{w} f P).obj F ≅ (restrictFunctorOn.{w, u} f P).obj F :=
  PresheafOfModules.isoMk
    (fun X => (ModuleCat.restrictScalarsId'App
      ((siteRestrictRingDiagram.{u} f P).app X).hom rfl _).symm)
    (by intro X Y g; ext x; rfl)

/-- **The degree-one Čech term on the site is the pushforward of [Stacks, Tag 06VA] there.**
The two scalar comparisons, the unit of base change and the injection into the pushout, are the
same map of ring diagrams; that is `AdequateFunctor.cechRingMap_eq_baseChangeRingHom`, which
can only be proved where the body of `AdequateFunctor.baseChangeAdjunction` is visible. -/
theorem cechOnceOn_eq_pushforwardOn
    (F : ModuleValuedFunctorOn.{w, u} (siteAlgebraInclusion.{u, u} A P)) :
    cechOnceOn f P hcl F = pushforwardOn f P hcl ((restrictZeroOn.{w} f P).obj F) :=
  congrArg (fun φ => (PresheafOfModules.pushforward φ).obj F)
    (congrArg (Functor.whiskerLeft (siteAlgebraInclusion.{u, u} A P).op.op)
      (cechRingMap_eq_baseChangeRingHom f))

/-- **The degree-one Čech term of an adequate functor on the site is adequate.** Its restriction
to the `A'`-algebras of the site is adequate by [Stacks, Tag 06V9] there,
`AdequateFunctor.IsAdequate.restrictBaseOn`, and the Čech term is its pushforward by
[Stacks, Tag 06VA] there, `AdequateFunctor.isAdequate_pushforwardOn`. This is
`AdequateFunctor.isAdequate_cechOnce` on the site's domain of algebras. -/
theorem isAdequate_cechOnceOn
    (G : ModuleValuedFunctorOn.{max u w, u} (siteAlgebraInclusion.{u, u} A P))
    (hG : IsAdequate.{max u w, u} (siteAlgebraInclusion.{u, u} A P) G) :
    IsAdequate.{max u w, u} (siteAlgebraInclusion.{u, u} A P) (cechOnceOn f P hcl G) := by
  have hrest : IsAdequate.{max u w, u} (siteAlgebraInclusion.{u, u} A' P)
      ((restrictZeroOn.{max u w} f P).obj G) := by
    refine (IsAdequate.restrictBaseOn.{max u w, u, u, u} f P G hG).of_iso ?_
    exact (restrictZeroOnIso.{max u w} f P _).trans
      ((restrictFunctorOn.{max u w, u} f P).mapIso
        (presheafOfModulesUliftIso.{u, max u w} _ G).symm)
  rw [cechOnceOn_eq_pushforwardOn f P hcl G]
  exact isAdequate_pushforwardOn.{w} f P hcl _ hrest

/-! ### The distinguished algebra matters only up to isomorphism -/

section CofanIso

variable {C : Type u₁} [Category.{v₁} C]

/-- Precomposing one leg of a colimit binary cofan with an isomorphism leaves it a colimit: the
coproduct of `Y` and `X` is also the coproduct of `Y` and anything isomorphic to `X`. -/
def binaryCofanIsColimitPrecompIso {X X' Y Z : C} (k : X' ⟶ X) [IsIso k]
    {g : Y ⟶ Z} {h : X ⟶ Z} (hc : IsColimit (BinaryCofan.mk g h)) :
    IsColimit (BinaryCofan.mk g (k ≫ h)) := by
  refine BinaryCofan.IsColimit.mk _
    (fun a b => BinaryCofan.IsColimit.desc (s := BinaryCofan.mk g h) hc a (inv k ≫ b))
    (fun {T} a b => ?_) (fun {T} a b => ?_) (fun {T} a b m hm₁ hm₂ => ?_)
  · change g ≫ BinaryCofan.IsColimit.desc (s := BinaryCofan.mk g h) hc a (inv k ≫ b) = a
    exact BinaryCofan.IsColimit.inl_desc (s := BinaryCofan.mk g h) hc a (inv k ≫ b)
  · change (k ≫ h) ≫ BinaryCofan.IsColimit.desc (s := BinaryCofan.mk g h) hc a (inv k ≫ b) = b
    calc (k ≫ h) ≫ BinaryCofan.IsColimit.desc (s := BinaryCofan.mk g h) hc a (inv k ≫ b)
        = k ≫ h ≫ BinaryCofan.IsColimit.desc (s := BinaryCofan.mk g h) hc a (inv k ≫ b) :=
          Category.assoc _ _ _
      _ = k ≫ inv k ≫ b := congrArg (fun z => k ≫ z)
          (BinaryCofan.IsColimit.inr_desc (s := BinaryCofan.mk g h) hc a (inv k ≫ b))
      _ = b := by rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  · have hdl : g ≫ BinaryCofan.IsColimit.desc (s := BinaryCofan.mk g h) hc a (inv k ≫ b) = a :=
      BinaryCofan.IsColimit.inl_desc (s := BinaryCofan.mk g h) hc a (inv k ≫ b)
    have hdr : h ≫ BinaryCofan.IsColimit.desc (s := BinaryCofan.mk g h) hc a (inv k ≫ b) =
        inv k ≫ b :=
      BinaryCofan.IsColimit.inr_desc (s := BinaryCofan.mk g h) hc a (inv k ≫ b)
    refine BinaryCofan.IsColimit.hom_ext (s := BinaryCofan.mk g h) hc ?_ ?_
    · change g ≫ m = g ≫ BinaryCofan.IsColimit.desc (s := BinaryCofan.mk g h) hc a (inv k ≫ b)
      exact hm₁.trans hdl.symm
    · change h ≫ m = h ≫ BinaryCofan.IsColimit.desc (s := BinaryCofan.mk g h) hc a (inv k ≫ b)
      refine Eq.trans ?_ hdr.symm
      calc h ≫ m = inv k ≫ k ≫ h ≫ m := (IsIso.inv_hom_id_assoc k (h ≫ m)).symm
        _ = inv k ≫ (k ≫ h) ≫ m :=
          congrArg (fun z => inv k ≫ z) (Category.assoc k h m).symm
        _ = inv k ≫ b := congrArg (fun z => inv k ≫ z) hm₂

end CofanIso

/-- The Čech condition of [Stacks, Tag 06VH] depends on the distinguished algebra only up to
isomorphism: the two coproducts it asks for are coproducts with that algebra, and
`AdequateFunctor.binaryCofanIsColimitPrecompIso` transports them.

This is what lets a `CechExactOn` proved at a concretely built algebra — the product of a
standard affine covering, say — be used at `AdequateFunctor.baseAlgebra` of the corresponding
ring map, whose algebra structure is `RingHom.toAlgebra` of the structure map and therefore a
different, isomorphic, object. -/
theorem CechExactOn.of_iso {D : Type u₁} [Category.{v₁} D]
    {ι : D ⥤ CommAlgCat.{u} A} {G : ModuleValuedFunctorOn.{w} ι} {X Y : D} (e : Y ≅ X)
    (h : CechExactOn ι G X) : CechExactOn ι G Y := by
  intro B B₁ B₂ iB iA jB jA q hc₁ hc₂ h₁ h₂
  refine h B B₁ B₂ iB (e.inv ≫ iA) jB (e.inv ≫ jA) q ?_ ?_ h₁ ?_
  · rw [ι.map_comp]
    exact binaryCofanIsColimitPrecompIso (ι.map e.inv) hc₁
  · rw [ι.map_comp]
    exact binaryCofanIsColimitPrecompIso (ι.map e.inv) hc₂
  · rw [Category.assoc, h₂]

/-! ### The Čech diagram on the site -/

variable (F : ModuleValuedFunctorOn.{w, u} (siteAlgebraInclusion.{u, u} A P))

/-- The augmentation `F ⟶ F(- ⊗_A A')` of the Čech diagram, on the site's algebras. -/
def cechAugmentationOn : F ⟶ cechOnceOn f P hcl F where
  app X := F.map ((cechUnitOn f P hcl).app X.unop.unop).op.op
  naturality := by
    intro X Y g
    ext x
    change F.map ((cechUnitOn f P hcl).app Y.unop.unop).op.op (F.map g x) =
      F.map (((cechBaseChangeOn f P hcl).op.op).map g)
        (F.map ((cechUnitOn f P hcl).app X.unop.unop).op.op x)
    have hn := congrArg (fun k => k.op.op)
      ((cechUnitOn f P hcl).naturality g.unop.unop)
    rw [← F.map_comp_apply g (((cechUnitOn f P hcl).app Y.unop.unop).op.op) x]
    rw [← F.map_comp_apply ((cechUnitOn f P hcl).app X.unop.unop).op.op
      (((cechBaseChangeOn f P hcl).op.op).map g) x]
    exact F.congr_map_apply hn x

/-- The Čech map induced by the unit on the inner factor, on the site's algebras. -/
def cechMapInnerOn : cechOnceOn f P hcl F ⟶ cechTwiceOn f P hcl F where
  app X := (cechOnceOn f P hcl F).map ((cechUnitOn f P hcl).app X.unop.unop).op.op
  naturality := by
    intro X Y g
    ext x
    change (cechOnceOn f P hcl F).map ((cechUnitOn f P hcl).app Y.unop.unop).op.op
        ((cechOnceOn f P hcl F).map g x) =
      (cechOnceOn f P hcl F).map (((cechBaseChangeOn f P hcl).op.op).map g)
        ((cechOnceOn f P hcl F).map ((cechUnitOn f P hcl).app X.unop.unop).op.op x)
    have hn := congrArg (fun k => k.op.op)
      ((cechUnitOn f P hcl).naturality g.unop.unop)
    rw [← (cechOnceOn f P hcl F).map_comp_apply g
      (((cechUnitOn f P hcl).app Y.unop.unop).op.op) x]
    rw [← (cechOnceOn f P hcl F).map_comp_apply
      (((cechUnitOn f P hcl).app X.unop.unop).op.op)
      (((cechBaseChangeOn f P hcl).op.op).map g) x]
    exact (cechOnceOn f P hcl F).congr_map_apply hn x

/-- The Čech map induced by the unit on the outer factor, on the site's algebras. -/
def cechMapOuterOn : cechOnceOn f P hcl F ⟶ cechTwiceOn f P hcl F :=
  (PresheafOfModules.pushforward (cechRingMapOn f P hcl)).map (cechAugmentationOn f P hcl F)

/-- The Čech differential on the site's algebras, the difference of the two maps into the
degree-two term. -/
def cechDifferentialOn : cechOnceOn f P hcl F ⟶ cechTwiceOn f P hcl F :=
  cechMapInnerOn f P hcl F - cechMapOuterOn f P hcl F

/-! ### Exactness of the Čech diagram on the site -/

variable (hA' : algebraInSite.{u, u} A P (baseAlgebra f))

/-- The base ring `A'` as an algebra of the site. -/
abbrev baseAlgebraOn : AlgebrasInSite.{u, u} A P := ⟨baseAlgebra f, hA'⟩

/-- The inclusion of `A'` into the base change of an algebra of the site. -/
def cechBaseInclusionOn (B : AlgebrasInSite.{u, u} A P) :
    baseAlgebraOn f P hA' ⟶ (cechBaseChangeOn f P hcl).obj B :=
  ObjectProperty.homMk (cechBaseInclusion f B.obj)

/-- The Čech condition on the site, read at a single algebra of the site: the augmentation is
injective and a section killed by the differential comes from the base. This is
`AdequateFunctor.cechExactAt` on the site's domain of algebras, and the binary coproducts it
feeds to `AdequateFunctor.CechExactOn` are those of `AdequateFunctor.cechCofanIsColimit`, the
domain being full. -/
theorem cechExactAtOn
    (hexact : CechExactOn (siteAlgebraInclusion.{u, u} A P) F (baseAlgebraOn f P hA'))
    (B : AlgebrasInSite.{u, u} A P) :
    Function.Injective (F.map ((cechUnitOn f P hcl).app B).op.op) ∧
      ∀ y : F.obj (op (op ((cechBaseChangeOn f P hcl).obj B))),
        (F.map ((cechUnitOn f P hcl).app
              ((cechBaseChangeOn f P hcl).obj B)).op.op y =
            F.map ((cechBaseChangeOn f P hcl).map
              ((cechUnitOn f P hcl).app B)).op.op y ↔
          ∃ x : F.obj (op (op B)), F.map ((cechUnitOn f P hcl).app B).op.op x = y) := by
  let B₁ := (cechBaseChangeOn f P hcl).obj B
  let iB := (cechUnitOn f P hcl).app B
  let iA := cechBaseInclusionOn f P hcl hA' B
  let jB := (cechUnitOn f P hcl).app B₁
  let jA := cechBaseInclusionOn f P hcl hA' B₁
  let q := (cechBaseChangeOn f P hcl).map iB
  have hunit : iB ≫ q = iB ≫ jB :=
    ObjectProperty.hom_ext (P := algebraInSite.{u, u} A P)
      ((cechUnit f).naturality ((cechUnit f).app B.obj)).symm
  have hbase : iA ≫ q = jA :=
    ObjectProperty.hom_ext (P := algebraInSite.{u, u} A P)
      (cechBaseInclusion_naturality f ((cechUnit f).app B.obj))
  simpa [B₁, iB, iA, jB, jA, q] using
    hexact B B₁ ((cechBaseChangeOn f P hcl).obj B₁) iB iA jB jA q
      (cechCofanIsColimit f B.obj) (cechCofanIsColimit f B₁.obj) hunit hbase

/-- A section is killed by the Čech differential exactly when its two images in the degree-two
term agree. -/
theorem cechDifferentialOn_app_eq_iff (B : AlgebrasInSite.{u, u} A P)
    (y : F.obj (op (op ((cechBaseChangeOn f P hcl).obj B)))) :
    (cechDifferentialOn f P hcl F).app (op (op B)) y = 0 ↔
      F.map ((cechUnitOn f P hcl).app
          ((cechBaseChangeOn f P hcl).obj B)).op.op y =
        F.map ((cechBaseChangeOn f P hcl).map
          ((cechUnitOn f P hcl).app B)).op.op y := by
  change (cechMapInnerOn f P hcl F).app (op (op B)) y -
    (cechMapOuterOn f P hcl F).app (op (op B)) y = 0 ↔ _
  exact sub_eq_zero.trans eq_comm

/-- The Čech condition gives exactness of the augmentation followed by the differential at a
single algebra of the site. -/
theorem cechPointExactAtOn
    (hexact : CechExactOn (siteAlgebraInclusion.{u, u} A P) F (baseAlgebraOn f P hA'))
    (B : AlgebrasInSite.{u, u} A P) :
    Function.Exact
        (((cechAugmentationOn f P hcl F).app (op (op B))).hom)
        (((cechDifferentialOn f P hcl F).app (op (op B))).hom) ∧
      Function.Injective
        (((cechAugmentationOn f P hcl F).app (op (op B))).hom) := by
  have h := cechExactAtOn f P hcl F hA' hexact B
  exact ⟨fun y => (cechDifferentialOn_app_eq_iff f P hcl F B y).trans (h.2 y), h.1⟩

/-- The augmentation composed with the Čech differential is zero. -/
theorem cechAugmentationOn_comp_cechDifferentialOn
    (hexact : CechExactOn (siteAlgebraInclusion.{u, u} A P) F (baseAlgebraOn f P hA')) :
    cechAugmentationOn f P hcl F ≫ cechDifferentialOn f P hcl F = 0 := by
  ext X x
  change (((cechDifferentialOn f P hcl F).app X).hom
    (((cechAugmentationOn f P hcl F).app X).hom x)) = 0
  exact (cechPointExactAtOn f P hcl F hA' hexact X.unop.unop).1.apply_apply_eq_zero x

/-- Under the Čech condition the augmentation exhibits `F` as the kernel of the Čech
differential, on the site's algebras. -/
def cechAugmentationOnKernelIsLimit
    (hexact : CechExactOn (siteAlgebraInclusion.{u, u} A P) F (baseAlgebraOn f P hA')) :
    IsLimit (KernelFork.ofι (cechAugmentationOn f P hcl F)
      (cechAugmentationOn_comp_cechDifferentialOn f P hcl F hA' hexact)) := by
  apply PresheafOfModules.evaluationJointlyReflectsLimits
  intro X
  obtain ⟨h₁, h₂⟩ := cechPointExactAtOn f P hcl F hA' hexact X.unop.unop
  exact (KernelFork.isLimitMapConeEquiv
    (KernelFork.ofι (cechAugmentationOn f P hcl F)
      (cechAugmentationOn_comp_cechDifferentialOn f P hcl F hA' hexact))
    (PresheafOfModules.evaluation (algebraRingDiagramOn.{u}
      (siteAlgebraInclusion.{u, u} A P)) X)).symm
    (ModuleCat.isLimitKernelFork
      ((cechAugmentationOn f P hcl F).app X) ((cechDifferentialOn f P hcl F).app X) h₁ h₂)

/-- Under the Čech condition `F` is the kernel of its Čech differential, on the site's
algebras. -/
def cechAugmentationOnKernelIso
    (hexact : CechExactOn (siteAlgebraInclusion.{u, u} A P) F (baseAlgebraOn f P hA')) :
    F ≅ kernel (cechDifferentialOn f P hcl F) :=
  (cechAugmentationOnKernelIsLimit f P hcl F hA' hexact).conePointUniqueUpToIso
    (limit.isLimit (parallelPair (cechDifferentialOn f P hcl F) 0))

/-! ### Tag 06VH on the algebras of the site -/

include hcl in
/-- **[Stacks, Tag 06VH] on the site's domain of algebras.** Adequacy of a module-valued
functor on the `A`-algebras of a site descends through an exact Čech equalizer for a ring map
`A → A'` whose target is again an algebra of the site.

The inputs are those of `AdequateFunctor.isAdequate_of_descent`, each on the site's domain:
adequacy of the restriction of `F` to the `A'`-algebras of the site, the Čech condition in the
form `AdequateFunctor.CechExactOn` that a sheaf condition delivers, and — in place of the
ambient appeal to [Stacks, Tag 06V3] on all algebras — closure of adequacy under kernels on the
domain, which over a big site is
`Stacks.Adequate.affineAdequateKernels`. -/
theorem isAdequate_of_descent_on
    (G : ModuleValuedFunctorOn.{max u w, u} (siteAlgebraInclusion.{u, u} A P))
    (G' : ModuleValuedFunctorOn.{max u w, u} (siteAlgebraInclusion.{u, u} A' P))
    (hG' : IsAdequate.{max u w, u} (siteAlgebraInclusion.{u, u} A' P) G')
    (hrestrict : Nonempty (G' ≅ (restrictZeroOn.{max u w} f P).obj G))
    (hkernel : ∀ {X Y : ModuleValuedFunctorOn.{max u w, u}
        (siteAlgebraInclusion.{u, u} A P)} (φ : X ⟶ Y),
      IsAdequate.{max u w, u} (siteAlgebraInclusion.{u, u} A P) X →
      IsAdequate.{max u w, u} (siteAlgebraInclusion.{u, u} A P) Y →
      IsAdequate.{max u w, u} (siteAlgebraInclusion.{u, u} A P) (kernel φ))
    (hexact : CechExactOn (siteAlgebraInclusion.{u, u} A P) G (baseAlgebraOn f P hA')) :
    IsAdequate.{max u w, u} (siteAlgebraInclusion.{u, u} A P) G := by
  obtain ⟨e⟩ := hrestrict
  have hOnce : IsAdequate.{max u w, u} (siteAlgebraInclusion.{u, u} A P)
      (cechOnceOn f P hcl G) := by
    rw [cechOnceOn_eq_pushforwardOn f P hcl G]
    exact (isAdequate_pushforwardOn.{w} f P hcl G' hG').of_iso
      ((PresheafOfModules.pushforward (baseChangeRingHomOn f P hcl)).mapIso e.symm)
  have hTwice : IsAdequate.{max u w, u} (siteAlgebraInclusion.{u, u} A P)
      (cechTwiceOn f P hcl G) :=
    isAdequate_cechOnceOn.{w} f P hcl _ hOnce
  exact (hkernel (cechDifferentialOn f P hcl G) hOnce hTwice).of_iso
    (cechAugmentationOnKernelIso f P hcl G hA' hexact)

end AdequateFunctor

end
